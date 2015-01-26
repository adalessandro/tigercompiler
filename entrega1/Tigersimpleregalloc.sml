structure Tigersimpleregalloc :> Tigersimpleregalloc =
struct
	structure frame = Tigerframe
	open Tigerassem
	
	fun simpleregalloc (frm:frame.frame) (body:instr list) =
	let
		(* Temporarios que ya tienen color asignado (p.ej, el temporario que representa a rax) *)
		val precolored = frame.specialregs @ frame.argregs
		(* Temporarios que se pueden usar (p.ej, el temporario que representa a rax. Diferencia con precolored: el temporario que representa a rbp no se puede usar) *)
		val asignables = frame.generalregs
		(* movaMem crea una instrucción que mueve un temporario a memoria. movaTemp, de memoria a un temporario.*)
		fun movaMem(temp, mempos) =
			let val desp = if mempos<0 then " - " ^ Int.toString(~mempos) else if mempos>0 then " + " ^ Int.toString(mempos) else ""
			in  OPER {assem="str     `s0, [`d0, #" ^ desp ^ "]", src=[temp], dest=[frame.fp], jump=NONE}
			end
		fun movaTemp(mempos, temp) =
			let	val desp = if mempos<0 then " - " ^ Int.toString(~mempos) else if mempos>0 then " + " ^ Int.toString(mempos) else ""
			in  OPER {assem="ldr     `d0, [`s0, #" ^ desp ^ "]", src=[frame.fp], dest=[temp], jump=NONE}
			end
		val temps =
			let
				val tempList = 
					let
						fun f (OPER r, tmplist) = List.concat [#dest r, #src r, tmplist]
						| f (LABEL _, tmplist) = tmplist
						| f (MOVE r, tmplist) = List.concat [#dest r, #src r, tmplist]
					in
						List.foldr f [] body
					end
				val s = Splayset.addList(Splayset.empty String.compare, tempList)
				val precoloredSet = Splayset.addList(Splayset.empty String.compare, precolored)
			in
				Splayset.listItems(Splayset.difference(s, precoloredSet))
			end

		val accesses = map (fn T => let val offset = frame.allocLocal frm true 
                                        val n = (case offset of
                                                      frame.InFrame n => n
                                                    | _ => raise Fail("No debería suceder. Tigersimpleregalloc.accesses."))
                                    in (T, n) end) temps
		fun getFramePos T =
			let
				fun gfp T [] = raise Fail("Temporario no encontrado: "^T)
				| gfp T ((a,b)::xs) = if a=T then b else gfp T xs
			in
				gfp T accesses
			end

		fun rewriteInstr (OPER {assem, dest, src, jump}) =
			let
				val eset = Splayset.empty String.compare
				val precoloredSet = Splayset.addList(eset, precolored)
				val asignablesSet = Splayset.addList(eset, asignables)
				val dstset = Splayset.addList(eset, dest)
				val srcset = Splayset.addList(eset, src)
				val colores = Splayset.listItems(Splayset.difference(asignablesSet, Splayset.union(dstset, srcset)))
				val uncolored = Splayset.listItems(Splayset.difference(Splayset.union(dstset, srcset), precoloredSet))

				val N = length(uncolored)
				val tempcols = ListPair.zip(uncolored, List.take(colores, N))
				fun getTempCol T =
				let
					fun gtc T [] = if Splayset.member(precoloredSet, T) then T else raise Fail("Temporario no encontrado: "^T)
					| gtc T ((a,b)::xs) = if a=T then b else gtc T xs
				in
					gtc T tempcols
				end

				val (prevMovs, posMovs) =
				let
					fun mkgetMov T = movaTemp(getFramePos T, getTempCol T)
					fun mksetMov T = movaMem(getTempCol T, getFramePos T)
					fun filterPC T = not(Splayset.member(precoloredSet, T))
				in
					(map mkgetMov (List.filter filterPC src), map mksetMov (List.filter filterPC dest))
				end
				val newdst = map getTempCol dest
				val newsrc = map getTempCol src
				val newinstr = OPER {assem=assem, dest=newdst, src=newsrc, jump=jump}
			in
				List.concat [prevMovs, [newinstr], posMovs]
			end
		  | rewriteInstr (LABEL l) = [LABEL l]
		  | rewriteInstr (MOVE {assem, dest, src}) =
			let
				val precoloredSet = Splayset.addList(Splayset.empty String.compare, precolored)
                val destSet = Splayset.addList(Splayset.empty String.compare, dest)
                val srcSet = Splayset.addList(Splayset.empty String.compare, src)
			in
				(* if Splayset.member(precoloredSet, dest) andalso Splayset.member(precoloredSet, src) then [OPER {assem=assem, dest=[dest], src=[src], jump=NONE}] *)
				if Splayset.isSubset(destSet, precoloredSet) andalso Splayset.isSubset(srcSet, precoloredSet) then [OPER {assem=assem, dest=dest, src=src, jump=NONE}]
				(* else if Splayset.member(precoloredSet, dest) then [movaTemp(getFramePos src, dest)] *)
				else if Splayset.isSubset(destSet, precoloredSet) then [movaTemp(getFramePos (hd src), (hd dest))]
				(* else if Splayset.member(precoloredSet, src) then [movaMem(src, getFramePos dest)] *)
				else if Splayset.isSubset(srcSet, precoloredSet) then [movaMem((hd src), getFramePos (hd dest))]
				else
					let
						val color = hd(asignables)
					in
						[movaTemp(getFramePos (hd src), color), movaMem(color, getFramePos (hd dest))]
					end
			end
	in
		List.concat (map rewriteInstr body)
	end
end
