(*  Frame para ARMv7
 *
 *  |   argn            | fp+8+4*n
 *  |   ...             |
 *  |   arg1            | fp+12
 *  |   fp level (sl)   | fp+8
 *  |   fp ant          | fp+4
 *  |   retorno (lr)    | fp
 *  |   local 1         | fp-4
 *  |   ...             | ...
 *  |   local n         | fp-4*n
 *  |   ...             | ...
 *
 *)

structure Frame :> Frame = struct

open Tree
open Tigerextras

type level = int

type register = string

datatype access =
        InFrame of int
      | InReg of Temp.label

type frame = {
        name: string,
        formals: access list ref,
        locals: bool list,
        actualArg: int ref,
        actualLocal: int ref,
        actualReg: int ref
}

datatype frag =
        PROC of {body : Tree.stm, frame : frame}
      | STRING of Temp.label * string

datatype canonfrag =
        CPROC of {body : Tree.stm list, frame : frame}
      | CSTRING of Temp.label * string


(* ARM specific constants *)
val r0 = "r0"               (* general purpose regs *)
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

val fp = "fp"               (* frame pointer *) (* r11 *)
val sp = "sp"               (* stack pointer *) (* r13 *)
val rv = r0                 (* return value  *) (* r0 *)
val lr = "lr"               (* link register *) (* r14 *)
val pc = "pc"               (* program counter *) (* r15 *)

val generalregs = [r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10]
val genregslen = List.length generalregs
val argregs = [r0, r1, r2, r3]
val argregslen = List.length argregs
val specialregs = [rv, fp, sp, lr, pc]
val specialregslen = List.length specialregs
val callersaves = [r0, r1, r2, r3]
val calleesaves = [r4, r5, r6, r7, r8, r9, r10]

val wSz = 4                 (* word size in bytes *)
val fpPrev = 0              (* offset (bytes) - FP from caller *)
val fpPrevLev = 2*wSz       (* offset (bytes) - FP from upper level *)

val argsInicial = 0         (* int - SL is always the first argument *)
val localsInicial = 0       (* int *)
val regInicial = 1          (* int *)

val argsOffInicial = 3*wSz  (* bytes - after the args we pushed {lr, fp, r0} *)
val argsGap = wSz           (* bytes *)
val localsGap = ~wSz        (* bytes - it's a FULL descending stack *)

(* Auxiliary functions *)
fun isInReg (InReg _) = true
  | isInReg _ = false

fun isInFrame (InFrame _) = true
  | isInFrame _ = false

(* Frame definition *)
fun newFrame {name, escapes} =
        {   name = name,
            formals = ref [],
            locals = [],
            actualArg = ref argsInicial,
            actualLocal = ref localsInicial,
            actualReg = ref regInicial
        }

fun name (f: frame) = #name f

fun allocLocal (f: frame) escape = 
        if escape then
            let val offset = localsGap - (!(#actualLocal f)) * wSz
            in
                #actualLocal f := (!(#actualLocal f) + 1);
                InFrame offset
            end
        else
            InReg (Temp.newtemp())

fun allocArg (f: frame) escape =
        let val acc = 
                    if escape orelse (!(#actualReg f)) >= argregslen then
                        let val offset = argsOffInicial + (!(#actualArg f)) * wSz
                        in
                            #actualArg f := (!(#actualArg f)) + 1;
                            InFrame offset
                        end
                    else (
                        #actualReg f := (!(#actualReg f)) + 1;
                        InReg (Temp.newtemp())
                    )
        in
            #formals f := (!(#formals f)) @ [acc];
            acc
        end

fun formals (frm : frame) = !(#formals frm)

fun maxRegFrame (f: frame) = !(#actualReg f)

fun exp(InFrame k) = MEM(BINOP(PLUS, TEMP(fp), CONST k))
  | exp(InReg l) = TEMP l

fun externalCall(s, l) = CALL (NAME s, l)

fun makeString(l, s) =
        let val lab = if (l = "") then "" else l ^ ":\n"
            val str = if (s = "") then "" else "\t" ^ s ^ "\n"
        in
            lab ^ str
        end

fun setDirectives prog strs =
        let val strs' = (String.concat o List.map makeString) strs
            val headers = "\t.global _tigermain\n"
        in
            headers ^ strs' ^ prog
        end

(*  ProcEntryExit1 - (p. 261)
 *  For each incoming register parameter, move it to the place from which it is seen from within
 *  the within the function. This could be a frame location (for escaping parameters) or a fresh
 *  temporary.
 *  It should move callee-save (and return-address) register to new tomporaries, and on exit, it
 *  should move them back.
 *)
fun procEntryExit1 (frame : frame, body : Tree.stm) =
        let fun calleemove r =
                    let val t = Temp.newtemp()
                    in
                        (MOVE (TEMP t, TEMP r), MOVE (TEMP r, TEMP t))
                    end
            val calleemoves = List.map calleemove calleesaves
            val calleestores = List.map #1 calleemoves
            val calleefetchs = List.map #2 calleemoves
            val argtemps = List.map exp (List.filter isInReg (formals frame))
            val pairs = ListPair.zip (argtemps, List.tl argregs)
            fun argmove (t, r) = MOVE (t, TEMP r)
            val argmoves = List.map argmove pairs
        in
            seq (calleestores @ argmoves @ [body] @ calleefetchs)
        end

(*  ProcEntryExit2 - (p. 208)
 *  Appends a sink instruction to the function body to tell the register allocator that certain
 *  registers are live at procedure exit.
 *)
fun procEntryExit2 (frame : frame, instrs : Assem.instr list) =
        let val sink = Assem.OPER {assem = "", dest = [], src = rv :: calleesaves, jump = NONE}
        in
            instrs @ [sink]
        end

(*  ProcEntryExit3 - (p. 261)
 *  Creates the procedure prologue and epilogue assembly language.
 *  Adds stack pointer adjustment.
 *)
fun procEntryExit3 (instrs : Assem.instr list, frame : frame) =
        let val prolog = [
                    Assem.OPER {assem = "stmfd   sp!, {r0}", dest = [], src = [], jump = NONE},
                    Assem.OPER {assem = "stmfd   sp!, {fp, lr}", dest = [], src = [], jump = NONE},
                    Assem.OPER {assem = "mov     fp, sp", dest = [], src = [], jump = NONE}
                ]
            val epilog = [
                    Assem.OPER {assem = "mov     sp, fp", dest = [], src = [], jump = NONE},
                    Assem.OPER {assem = "ldmfd   sp!, {fp, lr}", dest = [], src = [], jump = NONE},
                    Assem.OPER {assem = "add     sp, sp, #4", dest = [], src = [], jump = NONE},
                    Assem.OPER {assem = "bx      lr", dest = [], src = [], jump = NONE}
                ]
            val offset = (!(#actualLocal frame)) * wSz
            val locals_gap =
                    if offset <> 0 then
                        [Assem.OPER {assem = "sub     sp, sp, " ^ Assem.const(offset),
                                     dest = [], src = [], jump = NONE}]
                    else []
            val (funlab, rest, lastjump) = (
                    [List.hd instrs],
                    List.tl (List.take (instrs, List.length instrs - 3)),
                    List.drop (instrs, List.length instrs - 3)
                )
        in
            {   prolog = "@ prologo\n",
                body = funlab @ prolog @ locals_gap @ rest @ epilog @ lastjump,
                epilog = "@ epilogo\n"
            }
        end


(* Extras *)
fun printAccess (acc : access) =
        case acc of
        InFrame x => (print "InFrame"; printint x)
      | InReg lab => (print "InReg"; print lab)

fun printFrame (frame : frame) = (
        print "FRAME:\n";
        print "name: "; print (#name frame); print "\n";
        print "formals: " ; printlist printAccess (!(#formals frame));
        print "locals: "; printlist printbool (#locals frame);
        print "actualArg: "; (printint o ! o #actualArg) frame; print "\n";
        print "actualLocal: "; (printint o ! o #actualLocal) frame; print "\n";
        print "actualReg: "; (printint o ! o #actualReg) frame; print "\n"
    )

fun frag2str (PROC {body=b, frame=f}) = "PROC: " ^ Tigerit.tree(b) ^ "\n"
  | frag2str (STRING (l, s)) = "STRING: " ^ l ^ " - " ^ s ^ "\n"

fun printfrag f = print (frag2str f)

fun canonfrag2str (CPROC {body=bs, frame=f}) =
        "CPROC: ---------------------\n" ^ (String.concat o List.map Tigerit.tree) bs
  | canonfrag2str (CSTRING (l, s)) =
        "CSTRING: " ^ l ^ " - " ^ s ^ "\n"

fun printcanonfrag f = print (canonfrag2str f)

end
