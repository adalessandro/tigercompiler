structure Simpleregalloc :> Simpleregalloc =
struct

structure Set = Splayset

open Assem
open Tigerextras

fun debug x = if (!Tigerextras.enable_debug) andalso Tigerextras.simpleregalloc_debug then print x else ()

(* Auxiliary functions *)
fun set_safedelete (s, i) = (
        Set.delete (s, i)
        handle NotFound => s
  )


(* movaTemp, de memoria a un temporario.*)
fun movaTemp (mempos, temp) =
        let val offset = ", " ^ Assem.const mempos
            val instr =
                    OPER {assem = "ldr     `d0, [`s0" ^ offset ^ "]",
                          src = [Frame.fp],
                          dest = [temp],
                          jump = NONE
                         }
        in
            [instr]
        end

(* movaMem crea una instrucción que mueve un temporario a memoria. *)
fun movaMem (temp, mempos) =
        let val offset = ", " ^ Assem.const mempos
            val instr =
                    OPER {assem = "str     `s0, [`s1" ^ offset ^ "]",
                          src = [temp, Frame.fp],
                          dest = [],
                          jump = NONE
                         }
        in
            [instr]
        end

(* simpleregalloc body frm spilledTemp
 *      Reemplaza todas las ocurrencias de spilledTemp por un nuevo temporario (o registro)
 *      agregando un fetch y store, antes y después de cada instrucción correspondiente.
 *      Hace esto para las instrucciones que tienen a spilledTemp en dest o src.
 *
 *      Requiere spilledTemp no debe ser precoloreado. Esto es un invariante previo?
 *)
fun simpleregalloc spilledTemp ((body : instr list), (frm : Frame.frame)) =
        let val _ = debug ("simpleregalloc (" ^ spilledTemp  ^ ")\n")
            (* Temporarios que se pueden usar (p.ej, el temporario que representa a rax. 
             * Diferencia con precolored: el temporario que representa a rbp no se puede usar) *)
            val asignables = Frame.generalregs
            val asignablesSet = Set.addList (Set.empty String.compare, asignables)

            fun is_spilledTemp x = (x = spilledTemp)
            fun do_rewrite i = List.exists is_spilledTemp (Assem.getTemps i)

            (* Offset en el frame para alojar el spilledTemp *)
            val opt_acc =
                    if List.exists do_rewrite body then
                        let val access = Frame.allocLocal frm true
                        in
                            case access of
                            Frame.InFrame n => SOME n
                          | _ => raise Fail("simpleregalloc.access: No debería suceder.")
                        end
                    else
                        NONE

            (* Se le pasa la instrs a spillear *)
            fun rewriteInstr (OPER {assem, dest, src, jump}) =
                    let val framepos = Option.valOf opt_acc
                        (* Asignación de colores *)
                        val colores = Set.listItems (set_safedelete (asignablesSet, spilledTemp))
                        (* Asignar un registro como color *)
                        (*val color = hd colores*)
                        (* Asignar un nuevo temp como color *)
                        val color = Temp.newtemp()
                        val _ = debug ("Creado temp: " ^ color ^
                                    ". Borrado temp: " ^ spilledTemp ^ "\n")
                        val issrc = List.exists (fn x => x = spilledTemp) src
                        val isdest = List.exists (fn x => x = spilledTemp) dest
                        fun replace t = if t = spilledTemp then color else t
                        val newsrc = if issrc then map replace src else src
                        val newdest = if isdest then map replace dest else dest
                        val prevMovs = if issrc then movaTemp (framepos, color) else []
                        val posMovs = if isdest then movaMem (color, framepos) else []
                        val newinstr = OPER {assem=assem, dest=newdest, src=newsrc, jump=jump}
                    in
                        prevMovs @ [newinstr] @ posMovs
                    end
              | rewriteInstr (LABEL l) = [LABEL l]
              | rewriteInstr (MOVE {assem, dest, src}) =
                    let val framepos = Option.valOf opt_acc
                        val tdest = hd dest
                        val tsrc = hd src
                        val instrs =
                                if tdest = spilledTemp then
                                    movaMem (tsrc, framepos)
                                else if tsrc = spilledTemp then
                                    movaTemp (framepos, tdest)
                                else
                                    raise Fail ("simpleregalloc.rewriteInstr: No debería suceder")
                    in
                        instrs
                    end
        in
            (List.concat (map (fn i => if do_rewrite i then rewriteInstr i else [i]) body), frm)
        end

end
