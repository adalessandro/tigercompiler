structure Tigerassem :> Tigerassem =
struct

structure T = Tigertree

type reg = string
type temp = Tigertemp.temp
type label = Tigertemp.label

datatype instr =
    OPER of {assem: string,
             dest: temp list,
             src: temp list,
             jump: label list option}
  | LABEL of {assem: string,
              lab: label}
  | MOVE of {assem: string,
             dest: temp list,
             src: temp list}
    
fun format f i = ""
fun const i = "#" ^ Int.toString(i)
fun flabel l = "=" ^ l

val ilist = ref []
fun emits x = ilist :=x::(!ilist)
fun result gen = let val t = Tigertemp.newtemp()
                 in gen t; t end

fun munchStm (T.MOVE ((T.CONST _), _)) = raise Fail "MOVE dest = CONST"
  | munchStm (T.MOVE ((T.NAME _), _)) = raise Fail "MOVE dest = NAME"
  | munchStm (T.MOVE ((T.TEMP d), (T.CONST i))) = 
        emits (OPER {assem = "movs    `d0, "^const(i), dest = [d], src = [], jump = NONE})
  | munchStm (T.MOVE ((T.TEMP d), (T.NAME l))) =
        emits (OPER {assem = "ldrs    `d0, "^flabel(l), dest = [d], src = [], jump = NONE})
  | munchStm (T.MOVE ((T.TEMP d), (T.TEMP s))) =
        emits (MOVE {assem = "movs    `d0, `s0", dest = [d], src = [s]})
  | munchStm (T.MOVE ((T.TEMP d), (T.BINOP (MUL, e1, e2)))) =
        let val (e1', e2') = (munchExp e1, munchExp e2)
            val (e1'', e2'') = if (d = e1') then (e2', e1') else (e1', e2')
        in  emits (OPER {assem = "muls    `d0, `s0, `s1", dest = [d], src = [e1'', e2''], jump = NONE})
        end
  | munchStm (T.MOVE ((T.TEMP d), (T.BINOP (PLUS, e1, e2)))) =
        let val (e1', e2') = (munchExp e1, munchExp e2)
        in  emits (OPER {assem = "adds    `d0, `s0, `s1", dest = [d], src = [e1', e2'], jump = NONE})
        end
  | munchStm (T.MOVE ((T.TEMP d), (T.BINOP (MINUS, e1, e2)))) =
        let val (e1', e2') = (munchExp e1, munchExp e2)
        in  emits (OPER {assem = "subs    `d0, `s0, `s1", dest = [d], src = [e1', e2'], jump = NONE})
        end
  | munchStm (T.MOVE ((T.TEMP d), (T.BINOP (DIV, e1, e2)))) =
        let val _ = munchStm (T.EXP (T.CALL (T.NAME "idiv", [e1, e2])))
        in  emits (OPER {assem = "movs    `d0, `s0", dest = [d], src = [Tigerframe.rv], jump = NONE})
        end
  | munchStm (T.MOVE ((T.TEMP d), (T.BINOP (AND, e1, e2)))) =
        let val (e1', e2') = (munchExp e1, munchExp e2)
        in  emits (OPER {assem = "ands    `d0, `s0, `s1", dest = [d], src = [e1', e2'], jump = NONE})
        end
  | munchStm (T.MOVE ((T.TEMP d), (T.BINOP (OR, e1, e2)))) =
        let val (e1', e2') = (munchExp e1, munchExp e2)
        in  emits (OPER {assem = "orrs    `d0, `s0, `s1", dest = [d], src = [e1', e2'], jump = NONE})
        end
  | munchStm (T.MOVE ((T.TEMP d), (T.BINOP (XOR, e1, e2)))) =
        let val (e1', e2') = (munchExp e1, munchExp e2)
        in  emits (OPER {assem = "eors    `d0, `s0, `s1", dest = [d], src = [e1', e2'], jump = NONE})
        end
  | munchStm (T.MOVE ((T.TEMP d), (T.BINOP (LSHIFT, e1, e2)))) =
        let val (e1', e2') = (munchExp e1, munchExp e2)
        in  emits (OPER {assem = "movs    `d0, `s0, lsl `s1", dest = [d], src = [e1', e2'], jump = NONE})
        end
  | munchStm (T.MOVE ((T.TEMP d), (T.BINOP (RSHIFT, e1, e2)))) =
        let val (e1', e2') = (munchExp e1, munchExp e2)
        in  emits (OPER {assem = "movs    `d0, `s0, lsr `s1", dest = [d], src = [e1', e2'], jump = NONE})
        end
  | munchStm (T.MOVE ((T.TEMP d), (T.BINOP (ARSHIFT, e1, e2)))) =
        let val (e1', e2') = (munchExp e1, munchExp e2)
        in  emits (OPER {assem = "movs    `d0, `s0, asr `s1", dest = [d], src = [e1', e2'], jump = NONE})
        end
  | munchStm (T.MOVE ((T.TEMP d), (T.MEM e1))) =
        let val e1' = munchExp e1
        in  emits (OPER {assem = "ldrs    `d0, `s0", dest = [d], src = [e1'], jump = NONE})
        end
  | munchStm (T.MOVE ((T.TEMP d), (T.CALL (ename, eargs)))) =
        let val _ = munchStm (T.EXP(T.CALL (ename, eargs)))
        in  emits (OPER {assem = "movs    `d0, `s0", dest = [d], src = [Tigerframe.rv], jump = NONE})
        end
  | munchStm (T.MOVE ((T.TEMP d), (T.ESEQ (s1, e1)))) =
        let val _ = munchStm s1
            val e1' = munchExp e1
        in  emits (OPER {assem = "movs    `d0, `s0", dest = [d], src = [e1'], jump = NONE})
        end
  | munchStm _ = ()

and munchExp e = "t"

end
