open Tigerabs

local (* Sort topolo'gico *)
	fun cmp(x, y) = x=y
	fun mem(x, []) = false
	| mem(x, y::l) = cmp(x, y) orelse mem(x, l)
	fun nexts(a, []) = []
	| nexts(a, (x, y)::pairs) =
		if cmp(a, x) then y::nexts(a, pairs) else nexts(a, pairs)
     infix -- ---
     infix rs ls
     fun x ls f = fn y => f(x,y)
     fun f rs y = fn x => f(x,y)
     fun i -- e = List.find (op rs e) i
     fun fst(x,_)= x and snd(_,y)= y
     fun lp --- e = List.find ((op <> rs e)o fst) lp
in
     fun buscaArrRecords lt =
          let  fun buscaRecs [] recs = recs
               |buscaRecs ((r as {name,ty=RecordTy _,...})::t) recs = buscaRecs t (r::recs)
               |buscaRecs ((r as {name,ty=ArrayTy _,...})::t) recs = buscaRecs t (r::recs)
               |buscaRecs (_::t) recs = buscaRecs t recs
          in buscaRecs lt [] end

	fun topsort graph =
		let	fun sort([], path, visited) = visited
			| sort(x::xs, path, visited) =
				if mem(x, path) then raise Fail "ciclo!"
				else sort(xs, path,
						if mem(x, visited) then visited
						else x::sort(nexts(x, graph), x::path, visited))
			val (starts, _) = ListPair.unzip graph
		in	sort(starts, [], []) end

     fun genPares lt =
          let
               val lres = buscaArrRecords lt
               fun genP [] res = res
               |genP ({name,ty=NameTy s}::t) res = genP t ((s,name)::res)
               |genP ({name,ty=ArrayTy s}::t) res = genP t ((s,name)::res)
               |genP ({name,ty=RecordTy lf}::t) res =
                    let                    
                         fun recorre ({typ=NameTy x,...}::t) =
                                   (case List.find ((op=rs x) o #name) lres of
                                         SOME _ => recorre t
                                         |_ => x::recorre t
                                   )
                             |recorre (_::t) = recorre t
                             |recorre [] = []
                         val res' = recorre lf
                         val res'' = List.map (fn x => (x,name)) res'
                    in genP t (res''@res) end
          in genP lt [] end

     fun procesa [] pares recs env = env
     |procesa (sorted as (h::l)) (pares:{name:symbol, ty:ty} list) recs env =
          let  fun filt h {name, ty=NameTy t} = h=t
               |filt h {name, ty=ArrayTy t} = h=t
               |filt h {name, ty=RecordTy lt} = List.exists ((h ls op=) o name) lt
               val (ps, ps') = List.partition (filt h) pares
               val ttopt = case List.find ((h ls op=) o #name) recs of
                              SOME {ty=RecordTy _, name} => NONE
                              |SOME {ty=ArrayTy _, name} => NONE
                              |SOME _ => NONE
                              |NONE => (case tigertab.tabBusca (h,env) of
                                         SOME t => SOME t
                                         |_ => raise Fail "No existe el tipo recursivo"
                                       )
               val env' = case ttopt of
                    SOME tt => List.foldr (fn ({name,ty=NameTy ty},env') 
                                             => tigertab.tabInserta (name, tt, env')
                                             |_ => raise Fail "ERROR INTERNO #"
                                          ) env ps
                    |_ => env
          in procesa t ps' recs env' end

end
(*
(* 3 *)
(* a esto hay que mejorarlo mucho! *)
fun integraTEnvs(env, env') =
	let	val res = fromTab env
		fun aux(c, v) = tabRInserta(c, v, res)
	in
		tabAplica(aux, env');
		res
	end
(*------------------------------*)

fun muestra(s, t)=
	let	fun aux(NameTy t) = print("NameTy "^t)
		| aux(ArrayTy t) = print("ArrayTy "^t)
		| aux(RecordTy l) =
			let	fun f{name, typ,...} =
					(print(name^" "); aux typ)
			in
				(print "RecordTy "; app f l)
			end
	in
		print s; print "    "; aux t; print "\n"
	end
fun string2Ty(s, t) = (NameTy s, t)
val t = colectaNameTy prueba
val l = List.map string2Ty (tabAList t);
val r = topsort l;
*)
