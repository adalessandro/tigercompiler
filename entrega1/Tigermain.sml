open Tigerlex
open Tigergrm
open Tigerescap
open Tigerseman
open BasicIO Nonstdio
open CantPrints

val debug = (fn x => print ("\n\n\nDEBUGMAIN: " ^ x ^ "\n\n\n"))

fun lexstream(is: instream) =
    Lexing.createLexer(fn b => fn n => buff_input is b 0 n);

fun errParsing(lbuf) = (print("Error en parsing!("
    ^(makestring(!num_linea))^
    ")["^(Lexing.getLexeme lbuf)^"]\n"); raise Fail "fin!")

fun main(args) =
    let fun arg(l, s) = (List.exists (fn x => x=s) l, List.filter (fn x => x<>s) l)
        val (arbol, l1) = arg(args, "-arbol")
        val (ir, l2) = arg(l1, "-ir") 
        val (canon, l3) = arg(l2, "-canon") 
        val (interp, l4) = arg(l3, "-interp") 
        val (code, l5) = arg(l4, "-code") 
        val (flow, l6) = arg(l5, "-flow") 
        val (interf, l7) = arg(l6, "-interf") 
        val entrada =
            case l7 of
                [n] => ((open_in n)
                    handle _ => raise Fail (n^" no existe!"))
              | [] => std_in
              | _ => raise Fail "opción desconocida!"

        (* Parsing input *)
        val lexbuf = lexstream entrada
        val expr = prog Tok lexbuf handle _ => errParsing lexbuf

        (* Semantic analisys and intermediate code *)
        val _ = Tigerescap.findEscape(expr)
        val _ = if arbol then Tigerpp.exprAst expr else ()
        val _ = Tigerseman.transProg(expr)
        val fraglist = Tigertrans.getResult() (* fragment list *)
        val _ = if ir then (print o String.concat o List.map Tigerframe.frag2str) fraglist else ()

        (* Basic blocks and trace *)
        val canonfraglist = Tigercanon.canonize fraglist (* lista de fragmentos canonizados *)
        val _ = if canon then (print o String.concat o List.map Tigerframe.canonfrag2str) canonfraglist else ()
        val (b,c) = Tigercanon.splitcanon canonfraglist 
            (*b: (Tigertree.stm list*Tigerframe.frame) list*)
            (*c: (Tigertemp.label*string) list*)
        (* val _ = print (String.concat (List.map (fn (x,y) => "(" ^ x ^ ", " ^ y ^ ")\n") c)) *)
        (* Interpreter *)
        val _ = if interp then Tigerinterp.inter true b c else () (* arg1 indica si el interprete ejecuta con debug *)
        
        (* Instruction selection *)
        val assemblocklist = List.map Tigerassem.munchStmBlock b 
        val _ = if code then (print o String.concat o List.map (Tigerassem.assemblock2str o List.rev)) assemblocklist else ()

        (* Liveness analisys *)
        val fgraph = Tigerflow.makeFGraph assemblocklist
        val _ = if flow then (((fn (Tigerflow.FGRAPH x) => Tigergraph.printGraph (#control x)) fgraph)) else []

(*        val igraph = Tigerinterference.makeIGraph fgraph *)
        val (intab, outtab) = (Tigerinterference.makeIGraph fgraph assemblocklist)
        val _ = List.map Tigergraph.entrypp (Tigertab.tabAList intab) 
(*        val _ = if interf then Tigergraph.printGraph igraph else [] *)

    in
        print "yes!!\n"
    end handle Fail s => print("Fail: "^s^"\n")

val _ = main(CommandLine.arguments())
