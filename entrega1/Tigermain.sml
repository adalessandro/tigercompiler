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
    let fun arg(l, s) =
            (List.exists (fn x => x=s) l, List.filter (fn x => x<>s) l)
        val (arbol, l1) = arg(args, "-arbol")
        val (escapes, l2) = arg(l1, "-escapes") 
        val (ir, l3) = arg(l2, "-ir") 
        val (canon, l4) = arg(l3, "-canon") 
        val (code, l5) = arg(l4, "-code") 
        val (flow, l6) = arg(l5, "-flow") 
        val (inter, l7) = arg(l6, "-inter") 
        val (cantprints, l8) = arg(l7, "-cantprints") 
        val (interference, l9) = arg(l8, "-interference") 
        val entrada =
            case l9 of
                [n] => ((open_in n)
                    handle _ => raise Fail (n^" no existe!"))
              | [] => std_in
              | _ => raise Fail "opción desconocida!"

        val lexbuf = lexstream entrada
        val expr = prog Tok lexbuf handle _ => errParsing lexbuf

        val _ = findEscape(expr)
        val _ = if arbol then Tigerpp.exprAst expr else ()
        val _ = if cantprints then print(Int.toString(CantPrints.cantPrintsExpr(expr))^"\n") else ()
        val _ = transProg(expr)

        fun insertr e (ls,rs) = (ls,e::rs)
        val fraglist = Tigertrans.getResult() (* fragment list *)
        val canonfraglist = Tigercanon.canonize fraglist
        fun insertl e (ls,rs) = (e::ls,rs)
        fun insertr e (ls,rs) = (ls,e::rs)
        fun splitcanon [] = ([],[])
          | splitcanon (x::xs) = 
                case x of
                     (Tigerframe.CSTRING s) => insertr s (splitcanon xs) 
                   | (Tigerframe.CPROC {body,frame}) => insertl (body, frame) (splitcanon xs) 
        val a = inter   
        val (b,c) = splitcanon canonfraglist 
    (*b: (Tigertree.stm list*Tigerframe.frame) list*)
    (*c: (Tigertemp.label*string) list*)
        val _ = if inter then Tigerinterp.inter a b c else ()
        val _ = if code then List.map ((List.map Tigerassem.munchStmP) o (#1)) b else []
        val _ = if code then (print "*************** Assembler CODE! ***************\n";
                 List.map (fn x => (print (Tigerassem.format x); print "\n")) (List.rev (!Tigerassem.ilist))) else []
        val ej1flow = Tigerflow.makeFGraph Tigerflow.ej1
        val _ = if flow then (((fn (Tigerflow.FGRAPH x) => Tigergraph.printGraph (#control x)) ej1flow); ()) else ()
        val _ = if interference then (Tigergraph.printGraph (Tigerinterference.makeIGraph ej1flow); ()) else ()
    in
        print "yes!!\n"
    end handle Fail s => print("Fail: "^s^"\n")

val _ = main(CommandLine.arguments())
