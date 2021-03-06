open Lex
open Grm
open Escap
open Seman
open Tigerextras
open BasicIO Nonstdio

val assem_filename = "output.s"
val bin_filename = "a.out"
val username = "root"
val host_ip = "192.168.0.103"

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
            val (final, l9) = arg (l8, "-final")
            val (debug, l10) = arg (l9, "-debug")
            val (runtime, l11) = arg (l10, "-runtime")
            val (scp, l12) = arg (l11, "-scp")
            val entrada =
                    case l12 of
                    [n] => ((open_in n) handle _ => raise Fail (n ^ " no existe!"))
                  | [] => std_in
                  | _ => raise Fail "opción desconocida!"

            (* General debug *)
            val _ = Tigerextras.enable_debug := debug

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
            (*val assemblocklist : Assem.instr list list = List.map Codegen.munchStmBlock blocks *)
            val assemblocklist : Assem.instr list list = Codegen.codegen blocks 
            val instrs = List.concat assemblocklist
            val _ = if code then (
                        List.map Assem.printAssem instrs; ()
                    ) else ()

            (* Flow, Liveness analisys and Coloring *)
            val bframes = List.map (#2) blocks
            val opts = [flow, interf, color]

            val final_assemblocklist = Coloring.coloring opts (ListPair.zip (assemblocklist, bframes))

            val final_instrs = List.concat final_assemblocklist

            (* It's the final printing! *)
            val _ = if final then (
                        List.map Assem.printAssem final_instrs; ()
                    ) else ()

            val final_prog = String.concat (List.map Assem.strAssem final_instrs)
    
            val final_prog' = Frame.setDirectives final_prog strs

            (* Output program to file *)
            val fd = TextIO.openOut assem_filename
            val _ = TextIO.output (fd, final_prog')
            val _ = TextIO.closeOut fd

            (* Build runtime *)
            val _ = if runtime then (
                        Process.system ("arm-linux-gnueabi-gcc -c runtime.c -o runtime.o");
                        ()
                    ) else ()

            (* Link, scp and remote execution *)
            val _ = if scp then (
                        Process.system ("arm-linux-gnueabi-gcc -g runtime.o -o " ^ bin_filename ^ " " ^ assem_filename);
                        println "starting scp";
                        Process.system ("scp " ^ bin_filename ^ " " ^ username ^ "@" ^ host_ip ^ ":");
                        Process.system ("ssh " ^ username ^ "@" ^ host_ip ^ " " ^ bin_filename);
                        ()
                    ) else ()
        in
            print "Ultra yes!!!\n"
        end

handle Fail s => print("Fail: " ^ s ^ "\n")

val _ = main(CommandLine.arguments())
