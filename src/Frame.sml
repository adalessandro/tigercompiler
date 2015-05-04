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

structure Frame :> Frame = struct

open Tree
open Tigerextras

type level = int

val fp = "fp"               (* frame pointer *) (* r11 *)
val sp = "sp"               (* stack pointer *) (* r13 *)
val rv = "r0"               (* return value  *) 
val lr = "lr"               (* link register *) (* r14 *)
val pc = "pc"               (* program counter *) (* r15 *)

val r0 = "r0"               (* args/general purpose regs *)
val r1 = "r1"
val r2 = "r2"
val r3 = "r3"
val r4 = "r4"
val r5 = "r5"
val r6 = "r6"
val r7 = "r7"
val r8 = "r8"
val r9 = "r9"
val r10 = "r10"
val generalregs = [r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10]
val genregslen = List.length generalregs

val wSz = 4                 (* word size in bytes *)
val log2WSz = 2             (* base two logarithm of word size in bytes *)
val fpPrev = 0              (* offset (bytes) *)
val fpPrevLev = 2*wSz       (* offset (bytes) *)
val argsInicial = 1         (* words *)
val argsOffInicial = 2      (* words *)
val argsGap = wSz           (* bytes *)
val regInicial = 1          (* reg *)
val localsInicial = 0       (* words *)
val localsGap = ~wSz        (* bytes *)
val calldefs = [rv]
val specialregs = [rv, fp, sp, lr, pc]
val argregs = [r0, r1, r2, r3]
val argregslen = List.length argregs
val callersaves = [r0, r1, r2, r3]
val calleesaves = [r4, r5, r6, r7, r8, r9, r10]

type frame = {
    name: string,
    formals: bool list,
    locals: bool list,
    actualArg: int ref,
    actualLocal: int ref,
    actualReg: int ref
}

type register = string

datatype access = InFrame of int | InReg of Temp.label

datatype frag = PROC of {body: Tree.stm, frame: frame}
              | STRING of Temp.label * string

(* frag despues de canonizarlo *)
datatype canonfrag = CPROC of {body: Tree.stm list, frame: frame}
                   | CSTRING of Temp.label * string (* ESTO NO DEBE USARSE NUNCA: ESTA MAL! *)

fun newFrame{name, formals} = {
    name=name,
    formals=formals,
    locals=[],
    actualArg=ref argsInicial,
    actualLocal=ref localsInicial,
    actualReg=ref regInicial
}

fun name(f: frame) = #name f

fun string(l, s) = l^Temp.makeString(s)^"\n"

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
        in if ret < argregslen
           then InReg (List.nth(argregs, ret)) (*consultar*)
           else InFrame ((ret-argregslen)*wSz)
        end

fun allocLocal (f: frame) b = 
    case b of
         true => let val ret = InFrame(!(#actualLocal f)*wSz+localsGap) (* InFrame(!(#actualLocal f)+localsGap) *)
                 in  #actualLocal f:=(!(#actualLocal f)-1); ret end
       | false => InReg(Temp.newtemp())

fun exp(InFrame k) = MEM(BINOP(PLUS, TEMP(fp), CONST k))
  | exp(InReg l) = TEMP l

fun externalCall(s, l) = CALL(NAME s, l)

fun procEntryExit1 (frame, body) = 
    let val prologo = seq(
                      [MOVE(TEMP sp, BINOP(MINUS, TEMP sp, CONST (2*wSz))), (* sp -= 8 *)
                       MOVE(MEM(BINOP(PLUS, TEMP sp, CONST wSz)), TEMP lr), (* [sp+4] = lr *)
                       MOVE(MEM(TEMP sp), TEMP fp), (* [sp] = fp *)
                       MOVE(TEMP fp, (BINOP(PLUS, TEMP sp, CONST wSz)))] (* fp = sp+4 *)
                      )
        val epilogo = seq(
                      [MOVE(TEMP sp, (BINOP(MINUS, TEMP fp, CONST wSz))), (* sp = fp-4 *)
                       MOVE(TEMP fp, MEM(TEMP sp)), (* fp = [sp] *)
                       MOVE(TEMP lr, MEM(BINOP(PLUS, TEMP sp, CONST wSz))), (* lr = [sp+4] *)
                       MOVE(TEMP sp, BINOP(PLUS, TEMP sp, CONST (2*wSz))), (* sp += 8 *)
                       (*MOVE(TEMP pc, TEMP lr)]*)
                       JUMP(TEMP lr, ["__RET_LABEL__"])] (* bx lr *)
                      )
    in
        seq([prologo, body, epilogo])
    end

fun printFrame (frame : frame) = (
        print "FRAME:\n";
        print "name: "; print (#name frame); print "\n";
        print "formals: " ; printlist printbool (#formals frame); print "\n";
        print "locals: "; printlist printbool (#locals frame); print "\n";
        print "actualArg: "; (print o Int.toString o ! o #actualArg) frame; print "\n";
        print "actualLocal: "; (print o Int.toString o ! o #actualLocal) frame; print "\n";
        print "actualReg: "; (print o Int.toString o ! o #actualReg) frame; print "\n"
    )

fun frag2str (PROC {body=b, frame=f}) = "PROC: " ^ Tigerit.tree(b) ^ "\n"
  | frag2str (STRING (l, s)) = "STRING: " ^ l ^ " - " ^ s ^ "\n"

fun printfrag f = print (frag2str f)

fun canonfrag2str (CPROC {body=bs, frame=f}) = "CPROC: ---------------------\n" ^
                                               (String.concat o List.map Tigerit.tree) bs
  | canonfrag2str (CSTRING (l, s)) = "CSTRING: " ^ l ^ " - " ^ s ^ "\n"

fun printcanonfrag f = print (canonfrag2str f)

end
