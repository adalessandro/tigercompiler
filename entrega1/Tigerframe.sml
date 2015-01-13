(*
    Frames para el 80386 (sin displays ni registers).

        |    argn    |  fp+4*(n+1)
        |    ...     |
        |    arg2    |  fp+16
        |    arg1    |  fp+12
        |   fp level |  fp+8
        |  retorno   |  fp+4
        |   fp ant   |  fp
        --------------  fp
        |   local1   |  fp-4
        |   local2   |  fp-8
        |    ...     |
        |   localn   |  fp-4*n
*)

structure Tigerframe :> Tigerframe = struct

open Tigertree

type level = int

val fp = "fp"               (* frame pointer *)
val sp = "sp"               (* stack pointer *)
val rv = "r0"               (* return value  *)
val ov = "ov"               (* overflow value (edx en el 386) *)
val wSz = 4                 (* word size in bytes *)
val log2WSz = 2             (* base two logarithm of word size in bytes *)
val fpPrev = 0              (* offset (bytes) *)
val fpPrevLev = 2*wSz         (* offset (bytes) *)
val argsInicial = 1         (* words *)
val argsOffInicial = 2      (* words *)
val argsGap = wSz           (* bytes *)
val regInicial = 1          (* reg *)
val localsInicial = 0       (* words *)
val localsGap = ~wSz        (* bytes *)
val calldefs = [rv]
val specialregs = [rv, fp, sp]
val argregs = ["r0", "r1", "r2", "r3"]
val argregslen = List.length argregs
val callersaves = []
val calleesaves = []

type frame = {
    name: string,
    formals: bool list,
    locals: bool list,
    actualArg: int ref,
    actualLocal: int ref,
    actualReg: int ref
}

fun printFrame (frame:frame) =
    let val _ = print "\n"
        val _ = (print ("name = " ^ (#name frame)))
        val _ = print "\n"
        val _ = (print "formals = " ; List.map (fn x => if x then print "T," else print "F,") (#formals frame))
        val _ = print "\n"
        val _ = (print "locals = " ; List.map (fn x => if x then print "T," else print "F,") (#locals frame))
        val _ = print "\n"
        val _ = (print "actualArg = " ; (print o Int.toString o ! o #actualArg) frame)
        val _ = print "\n"
        val _ = (print "actualLocal = " ; (print o Int.toString o ! o #actualArg) frame)
        val _ = print "\n"
        val _ = (print "actualReg = " ; (print o Int.toString o ! o #actualArg) frame)
        val _ = print "\n"
    in ()
    end 

type register = string

datatype access = InFrame of int | InReg of Tigertemp.label

datatype frag = PROC of {body: Tigertree.stm, frame: frame}
              | STRING of Tigertemp.label * string

(* frag despues de canonizarlo *)
datatype canonfrag = CPROC of {body: Tigertree.stm list, frame: frame}
                   | CSTRING of Tigertemp.label * string (* ESTO NO DEBE USARSE NUNCA: ESTA MAL! *)

fun newFrame{name, formals} = {
    name=name,
    formals=formals,
    locals=[],
    actualArg=ref argsInicial,
    actualLocal=ref localsInicial,
    actualReg=ref regInicial
}

fun name(f: frame) = #name f

fun string(l, s) = l^Tigertemp.makeString(s)^"\n"

fun formals({formals=f, name=n, ...}: frame) = (* agregar el caso 0 *) 
    let fun aux n m [] = []
          | aux n m (x::xs) = (case x of
                                    true => InFrame(n)::(aux (n+argsGap) m xs) 
                                  | false => InReg(Int.toString m)::(aux n (m+1) xs))
    in  
        aux (argsInicial+wSz*argsOffInicial) regInicial f
    end

fun maxRegFrame(f: frame) = !(#actualReg f)

fun allocArg (f: frame) b = 
    case b of
         true => let val ret = (!(#actualArg f)+argsOffInicial)*wSz
                     val _ = #actualArg f := !(#actualArg f)+1
                 in InFrame ret end
       | false => (*InReg(tigertemp.newtemp())*)
        let 
            val ret = !(#actualReg f)
            val _ = #actualReg f := !(#actualReg f) + 1 
        in InReg (Int.toString ret) (*consultar*)
        end

fun allocLocal (f: frame) b = 
    case b of
         true => let val ret = InFrame(!(#actualLocal f)*wSz+localsGap) (* InFrame(!(#actualLocal f)+localsGap) *)
                 in  #actualLocal f:=(!(#actualLocal f)-1); ret end
       | false => InReg(Tigertemp.newtemp())

fun exp(InFrame k) = MEM(BINOP(PLUS, TEMP(fp), CONST k))
  | exp(InReg l) = TEMP l

fun externalCall(s, l) = CALL(NAME s, l)

fun procEntryExit1 (frame, body) = body

end
