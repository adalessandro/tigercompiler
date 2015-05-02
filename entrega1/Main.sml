open Lex
open Grm
open Escap
open Seman
open Tigerextras
open BasicIO Nonstdio

fun lexstream (is: instream) =
        Lexing.createLexer (fn b => fn n => buff_input is b 0 n)

fun errParsing lbuf =
        let val ln = makestring(!num_linea)
            val buf = Lexing.getLexeme lbuf
        in
            print ("Error en parsing! (" ^ ln ^ ") [" ^ buf ^ "]\n");
            raise Fail "fin!"
        end

(* Program entry point *)
fun main args =
        let
            (* Command line options *)
            fun arg(l, s) = (List.exists (fn x => x = s) l, List.filter (fn x => x <> s) l)
            val (arbol, l1) = arg (args, "-arbol")
            val (ir, l2) = arg (l1, "-ir") 
            val (canon, l3) = arg (l2, "-canon") 
            val (interp, l4) = arg (l3, "-interp") 
            val (code, l5) = arg (l4, "-code") 
            val (flow, l6) = arg (l5, "-flow") 
            val (interf, l7) = arg (l6, "-interf") 
            val (color, l8) = arg (l7, "-color")
            val entrada =
                    case l8 of
                    [n] => ((open_in n) handle _ => raise Fail (n ^ " no existe!"))
                  | [] => std_in
                  | _ => raise Fail "opción desconocida!"

            (* Parsing input *)
            val lexbuf = lexstream entrada
            val expr = prog Tok lexbuf handle _ => errParsing lexbuf

            (* Semantic analisys and intermediate code *)
            val _ = Escap.findEscape(expr)
            val _ = if arbol then Tigerpp.exprAst expr else ()
            val _ = Seman.transProg(expr)
            val fraglist = Trans.getResult() (* fragment list *)
            val _ = if ir then (
                        List.map Frame.printfrag fraglist; ()
                    ) else ()

            (* Basic blocks and trace *)
            val canonfraglist = Canon.canonize fraglist (* lista de fragmentos canonizados *)
            val _ = if canon then (
                        List.map Frame.printcanonfrag canonfraglist; ()
                    ) else ()

            val (blocks : (Tree.stm list * Frame.frame) list, strs : (Temp.label * string) list) =
                    Canon.splitcanon canonfraglist 

            (* Interpreter *)
                (* arg1 indica si el interprete ejecuta con debug *)
            val _ = if interp then Interp.inter true blocks strs else ()
        
            (* Instruction selection *)
            val assemblocklist : Assem.instr list list = List.map Assem.munchStmBlock blocks 
            val instrs = (List.concat o List.map List.rev) assemblocklist
            val _ = if code then (
                        List.map Assem.printAssem instrs; ()
                    ) else ()

            (* Flow, Liveness analisys and Coloring *)
            val bframes = List.map (#2) blocks
            val opts = [flow, interf, color]
            val final_assemblocklist = Coloring.coloring opts (ListPair.zip (assemblocklist, bframes))
            val final_instrs = (List.concat o List.map List.rev) final_assemblocklist

            (* It's the final printing! *)
            val _ = (List.map Assem.printAssem final_instrs; ())
        in
            print "Ultra yes!!!\n"
        end

handle Fail s => print("Fail: " ^ s ^ "\n")

val _ = main(CommandLine.arguments())