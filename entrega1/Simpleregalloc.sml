structure Simpleregalloc :> Simpleregalloc =
struct

structure Set = Splayset

open Assem

(* movaTemp, de memoria a un temporario.*)
fun movaTemp (mempos, temp) =
        let val offset =
                    if mempos < 0 then
                        ", #-" ^ Int.toString (~mempos) 
                    else if mempos > 0 then
                        ", #" ^ Int.toString (mempos)
                    else ""
        in
            OPER {assem = "ldr     `d0, [`s0" ^ offset ^ "]",
                  src = [Frame.fp], 
                  dest = [temp], 
                  jump = NONE
                 }
        end

(* movaMem crea una instrucción que mueve un temporario a memoria. *)
fun movaMem (temp, mempos) =
        let val offset =
                    if mempos < 0 then
                        ", #-" ^ Int.toString (~mempos) 
                    else if mempos > 0 then
                        ", #" ^ Int.toString (mempos)
                    else ""
        in
            OPER {assem = "str     `s0, [`d0" ^ offset ^ "]",
                  src = [temp], 
                  dest = [Frame.fp], 
                  jump = NONE
                 }
        end

(* simpleregalloc body frm spilledTemp
 *      Reemplaza todas las ocurrencias de spilledTemp por un nuevo temporario (o registro)
 *      agregando un fetch y store, antes y después de cada instrucción correspondiente.
 *      Hace esto para las instrucciones que tienen a spilledTemp en dest o src.
 *
 *      Requiere spilledTemp no debe ser precoloreado. Esto es un invariante previo?
 *)
fun simpleregalloc spilledTemp ((body : instr list), (frm : Frame.frame)) =
        let (* Temporarios que se pueden usar (p.ej, el temporario que representa a rax. 
             * Diferencia con precolored: el temporario que representa a rbp no se puede usar) *)
            val asignables = Frame.generalregs
            val asignablesSet = Set.addList (Set.empty String.compare, asignables)

            (* Lista de offsets en el frame de los temporarios *)
            val framepos =
                    let val access = Frame.allocLocal frm true
                    in
                        case access of
                        Frame.InFrame n => n
                      | _ => raise Fail("simpleregalloc.access: No debería suceder.")
                    end

            fun is_spilledTemp x = (x = spilledTemp)
            fun do_rewrite i = List.exists is_spilledTemp (Assem.getTemps i)

            (* Se le pasa la instrs a spillear *)
            fun rewriteInstr (OPER {assem, dest, src, jump}) =
                    let (* Asignación de colores *)
                        val colores = Set.listItems (Set.delete (asignablesSet, spilledTemp))
                        (* Asignar un registro como color *)
                        (*val color = hd colores*)
                        (* Asignar un nuevo temp como color *)
                        val color = Temp.newtemp()
                        val prevMov = movaTemp (framepos, color)
                        val posMov = movaMem (color, framepos)
                        fun replace t = if t = spilledTemp then color else t
                        val newdest = map replace dest
                        val newsrc = map replace src
                        val newinstr = OPER {assem=assem, dest=newdest, src=newsrc, jump=jump}
                    in
                        [prevMov, newinstr, posMov]
                    end
              | rewriteInstr (LABEL l) = [LABEL l]
              | rewriteInstr (MOVE {assem, dest, src}) =
                    let val tdest = hd dest
                        val tsrc = hd src
                    in
                        if tdest = spilledTemp then
                            [movaMem (tsrc, framepos)]
                        else if tsrc = spilledTemp then
                            [movaTemp (framepos, tdest)]
                        else
                            raise Fail ("simpleregalloc.rewriteInstr: No debería suceder")
                    end
        in
            (List.concat (map (fn i => if do_rewrite i then rewriteInstr i else [i]) body), frm)
        end
end