structure Simpleregalloc :> Simpleregalloc =
struct
	structure frame = Frame
	open Assem
	
	fun simpleregalloc (frm:frame.frame) (body:instr list) =
	let
		(* Temporarios que ya tienen color asignado (p.ej, el temporario que representa a rax) *)
		val precolored = frame.specialregs @ frame.argregs
		(* Temporarios que se pueden usar (p.ej, el temporario que representa a rax. 
			Diferencia con precolored: el temporario que representa a rbp no se puede usar) *)
		val asignables = frame.generalregs

		(* movaMem crea una instrucción que mueve un temporario a memoria. *)
		fun movaMem(temp, mempos) =
			let val desp = if mempos<0 then " - " ^ Int.toString(~mempos) 
						   else if mempos>0 then " + " ^ Int.toString(mempos) else ""
			in  OPER {assem="str     `s0, [`d0, #" ^ desp ^ "]", 
					  src=[temp], 
					  dest=[frame.fp], 
					  jump=NONE}
			end

		(* movaTemp, de memoria a un temporario.*)
		fun movaTemp(mempos, temp) =
			let	val desp = if mempos<0 then " - " ^ Int.toString(~mempos) 
						   else if mempos>0 then " + " ^ Int.toString(mempos) else ""
			in  OPER {assem="ldr     `d0, [`s0, #" ^ desp ^ "]", 
					  src=[frame.fp], 
					  dest=[temp], 
					  jump=NONE}
			end

		val temps = (* Todos los temps de las instrs menos los precoloreados *)
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

		(* Lista de offsets en el frame de los temporarios *)
		val accesses = map (fn t => let val offset = frame.allocLocal frm true 
                                        val n = (case offset of
                                                      frame.InFrame n => n
                                                    | _ => raise Fail("No debería suceder. Simpleregalloc.accesses."))
                                    in (t, n) end) temps

		(* Devuelve la posición del temp en el frame *)
		fun getFramePos t =
			let
				fun gfp t [] = raise Fail("Temporario no encontrado: "^t)
				| gfp t ((a,b)::xs) = if a=t then b else gfp t xs
			in
				gfp t accesses
			end

		(* Se le pasa la instrs a spillear *)
		fun rewriteInstr (OPER {assem, dest, src, jump}) =
			let
				val eset = Splayset.empty String.compare
				val precoloredSet = Splayset.addList(eset, precolored)
				val asignablesSet = Splayset.addList(eset, asignables)
				val dstset = Splayset.addList(eset, dest)
				val srcset = Splayset.addList(eset, src)
				val colores = Splayset.listItems(
						Splayset.difference(asignablesSet, Splayset.union(dstset, srcset)))
				val uncolored = Splayset.listItems(
						Splayset.difference(Splayset.union(dstset, srcset), precoloredSet))

				val n = length(uncolored)
				val tempcols = ListPair.zip(uncolored, List.take(colores, n))

				fun getTempCol t =
					let
						fun gtc t [] = if Splayset.member(precoloredSet, t) then t 
									   else raise Fail("Temporario no encontrado: "^t)
					      | gtc t ((a,b)::xs) = if a=t then b else gtc t xs
					in
						gtc t tempcols
					end

				val (prevMovs, posMovs) =
					let
						fun mkgetMov t = movaTemp(getFramePos t, getTempCol t)
						fun mksetMov t = movaMem(getTempCol t, getFramePos t)
						fun filterPC t = not(Splayset.member(precoloredSet, t))
					in
						(map mkgetMov (List.filter filterPC src), 
						 map mksetMov (List.filter filterPC dest))
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
                val tdest = hd dest
                val tsrc = hd src
			in
				if Splayset.member(precoloredSet, tdest) andalso Splayset.member(precoloredSet, tsrc) then [OPER {assem=assem, dest=[tdest], src=[tsrc], jump=NONE}]
				else if Splayset.member(precoloredSet, tdest) then [movaTemp(getFramePos tsrc, tdest)]
				else if Splayset.member(precoloredSet, tsrc) then [movaMem(tsrc, getFramePos tdest)]
				else
					let
						val color = hd(asignables)
					in
						[movaTemp(getFramePos tsrc, color), movaMem(color, getFramePos tdest)]
					end
			end
	in
		List.concat (map rewriteInstr body)
	end
end
