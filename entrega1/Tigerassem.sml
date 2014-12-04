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

val ilist = ref []
fun emits x = ilist :=x::(!ilist)
fun result gen = let val t = Tigertemp.newtemp()
                 in gen t; t end

fun munchStm (T.MOVE ((T.CONST _), _)) = raise Fail "MOVE dest = CONST"
  | munchStm (T.MOVE ((T.NAME _), _)) = raise Fail "MOVE dest = NAME"
  | munchStm (T.MOVE ((T.TEMP d), (T.CONST i))) = 
        emits (OPER {assem = "movs "^d^", #"^Int.toString(i), dest = [d], src = [], jump = NONE})
  | munchStm (T.MOVE ((T.TEMP d), (T.NAME l))) =
        emits (OPER {assem = "ldrs "^d^", ="^l, dest = [d], src = [], jump = NONE})
  | munchStm (T.MOVE ((T.TEMP d), (T.TEMP s))) =
        emits (MOVE {assem = "movs "^d^", "^s, dest = [d], src = [s]})
  | munchStm (T.MOVE ((T.TEMP d), (T.BINOP (MUL, e1, e2)))) =
        let val (e1', e2') = (munchExp e1, munchExp e2)
            val (e1'', e2'') = if (d = e1') then (e2', e1') else (e1', e2')
        in  emits (OPER {assem = "muls "^d^", "^e1''^", "^e2'', dest = [d], src = [e1'', e2''], jump = NONE})
        end
  (*| munchStm (T.MOVE ((T.TEMP d), (T.BINOP (o, e1, e2)))) =
        let val o' = case o of
                          PLUS => "adds"
                        | MINUS => "subs"
                        | DIV => ""
                        | AND 
                        | OR
                        | LSHIFT 
                        | RSHIFT 
                        | ARSHIFT 
                        | XOR
        
  | munchStm (T.MOVE ((T.TEMP d), *)
  | munchStm _ = ()

and munchExp e = "t"

end
