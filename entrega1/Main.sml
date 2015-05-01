open Lex
open Grm
open Escap
open Seman
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
            val (liveness, l7) = arg (l6, "-liveness") 
            val (interf, l8) = arg (l7, "-interf") 
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

            val (b,c) = Canon.splitcanon canonfraglist 
                (*b: (Tree.stm list*Frame.frame) list*)
                (*c: (Temp.label*string) list*)

            (* Interpreter *)
                (* arg1 indica si el interprete ejecuta con debug *)
            val _ = if interp then Interp.inter true b c else ()
        
            (* Instruction selection *)
            val assemblocklist = List.map Assem.munchStmBlock b 
            val instrs = (List.concat o List.map List.rev) assemblocklist
            val _ = if code then (
                        List.map Assem.printAssem instrs; ()
                    ) else ()

            (* Flow analisys *)
            val fgraph = Flow.makeFGraph instrs
            val _ = if flow then Flow.printFlow ["control"] fgraph else ()

            (* Liveness analisys *)
            val bframes = List.map (#2) b
            (*val (igraph, outtab) = Interf.makeIGraph fgraph assemblocklist *)
            (*val _ = if liveness then List.map Graph.entrypp (Tab.tabAList outtab) else []*)
            (* val _ = if interf then Graph.printGraph igraph else [] *)

        in
            print "yes!!\n"
        end

handle Fail s => print("Fail: " ^ s ^ "\n")

val _ = main(CommandLine.arguments())
