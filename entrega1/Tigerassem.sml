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
   
val FALSE_LABEL = "__FALSE_LABEL__"
val RET_LABEL = "__RET_LABEL__"
val CALL_LABEL = "__CALL_LABEL__" 

fun labelpos x [] _ = NONE
  | labelpos x (y::ys) n =
         case y of
              LABEL {lab=lab, ...} => if lab = x then SOME n else labelpos x ys (n+1)
            | _ => labelpos x ys (n+1) 

(*fun format f i = ""*)
fun const i = "#" ^ Int.toString(i)
fun flabel l = "=" ^ l

val ilist = ref []
fun emits x = ilist :=x::(!ilist)
fun result gen = let val t = Tigertemp.newtemp()
                 in gen t; t end

val format =
    let fun speak(assem,dst,src,jump) =
            let fun saylab s = s 
                fun saytemp t = t 
                fun f(#"`":: #"s":: i::rest) = 
                        (explode(saytemp(List.nth(src,ord i - ord #"0"))) @ f rest)
                  | f( #"`":: #"d":: i:: rest) = 
                        (explode(saytemp(List.nth(dst,ord i - ord #"0"))) @ f rest)
                  | f( #"`":: #"j":: i:: rest) = 
                        (explode(saylab(List.nth(jump,ord i - ord #"0"))) @ f rest)
                  (*| f( #"`":: #"`":: rest) = #"`" :: f rest*)
                  | f( #"`":: _ :: rest) = raise Fail "bad Assem format"
                  | f(c :: rest) = (c :: f rest)
                  | f nil = nil 
            in implode(f(explode assem))
            end 
    in fn OPER{assem,dest,src,jump=NONE} => speak("\t"^assem,dest,src,nil)
        | OPER{assem,dest,src,jump=SOME j} => speak("\t"^assem,dest,src,j)
        | LABEL{assem,...} => "\t"^assem
        | MOVE{assem,dest,src} => speak("\t"^assem,dest,src,nil)
    end

fun assemblock2str is = "ASSEM BLOCK: ----------------------\n" ^
                        (String.concat o List.map (fn x => format x ^ "\n")) is

fun memStr x e1' = case x of
                        (T.CONST _) => e1'
                      | (T.NAME _) => e1'
                      | (T.TEMP _) => "[`s0]"
                      | (T.BINOP _) => "[`s0]"
                      | (T.ESEQ (st, ex)) => memStr ex e1'
                      | _ => raise Fail "memStr undefined"

fun munchStmBlock (ss, frame) = 
    let fun munchStm (T.MOVE ((T.CONST _), _)) = raise Fail "MOVE dest = CONST"
          | munchStm (T.MOVE ((T.NAME _), _)) = raise Fail "MOVE dest = NAME"
          | munchStm (T.MOVE ((T.TEMP d), (T.CONST i))) = 
                emits (OPER {assem = "movs    `d0, "^const(i), dest = [d], src = [], jump = NONE})
          | munchStm (T.MOVE ((T.TEMP d), (T.NAME l))) =
                emits (OPER {assem = "ldr     `d0, "^flabel(l), dest = [d], src = [], jump = NONE})
          | munchStm (T.MOVE ((T.TEMP d), (T.TEMP s))) =
                if d = Tigerframe.pc andalso s = Tigerframe.lr
                then emits (OPER {assem = "movs    `d0, `s0", dest = [d], src = [s], jump = SOME [RET_LABEL]})
                else emits (MOVE {assem = "movs    `d0, `s0", dest = [d], src = [s]})
          | munchStm (T.MOVE ((T.TEMP d), (T.BINOP (T.PLUS, e1, e2)))) =
                let val (e1', e2') = (munchExp e1, munchExp e2)
                in  emits (OPER {assem = "adds    `d0, `s0, `s1", dest = [d], src = [e1', e2'], jump = NONE})
                end
          | munchStm (T.MOVE ((T.TEMP d), (T.BINOP (T.MUL, e1, e2)))) =
                let val (e1', e2') = (munchExp e1, munchExp e2)
                    val (e1'', e2'') = if (d = e1') then (e2', e1') else (e1', e2')
                in  emits (OPER {assem = "muls    `d0, `s0, `s1", dest = [d], src = [e1'', e2''], jump = NONE})
                end
          | munchStm (T.MOVE ((T.TEMP d), (T.BINOP (T.MINUS, e1, e2)))) =
                let val (e1', e2') = (munchExp e1, munchExp e2)
                in  emits (OPER {assem = "subs    `d0, `s0, `s1", dest = [d], src = [e1', e2'], jump = NONE})
                end
          | munchStm (T.MOVE ((T.TEMP d), (T.BINOP (T.DIV, e1, e2)))) =
                let val _ = munchStm (T.EXP (T.CALL (T.NAME "idiv", [e1, e2])))
                in  emits (MOVE {assem = "movs    `d0, `s0", dest = [d], src = [Tigerframe.rv]})
                end
          | munchStm (T.MOVE ((T.TEMP d), (T.BINOP (T.AND, e1, e2)))) =
                let val (e1', e2') = (munchExp e1, munchExp e2)
                in  emits (OPER {assem = "ands    `d0, `s0, `s1", dest = [d], src = [e1', e2'], jump = NONE})
                end
          | munchStm (T.MOVE ((T.TEMP d), (T.BINOP (T.OR, e1, e2)))) =
                let val (e1', e2') = (munchExp e1, munchExp e2)
                in  emits (OPER {assem = "orrs    `d0, `s0, `s1", dest = [d], src = [e1', e2'], jump = NONE})
                end
          | munchStm (T.MOVE ((T.TEMP d), (T.BINOP (T.XOR, e1, e2)))) =
                let val (e1', e2') = (munchExp e1, munchExp e2)
                in  emits (OPER {assem = "eors    `d0, `s0, `s1", dest = [d], src = [e1', e2'], jump = NONE})
                end
          | munchStm (T.MOVE ((T.TEMP d), (T.BINOP (T.LSHIFT, e1, e2)))) =
                let val (e1', e2') = (munchExp e1, munchExp e2)
                in  emits (OPER {assem = "movs    `d0, `s0, lsl `s1", dest = [d], src = [e1', e2'], jump = NONE})
                end
          | munchStm (T.MOVE ((T.TEMP d), (T.BINOP (T.RSHIFT, e1, e2)))) =
                let val (e1', e2') = (munchExp e1, munchExp e2)
                in  emits (OPER {assem = "movs    `d0, `s0, lsr `s1", dest = [d], src = [e1', e2'], jump = NONE})
                end
          | munchStm (T.MOVE ((T.TEMP d), (T.BINOP (T.ARSHIFT, e1, e2)))) =
                let val (e1', e2') = (munchExp e1, munchExp e2)
                in  emits (OPER {assem = "movs    `d0, `s0, asr `s1", dest = [d], src = [e1', e2'], jump = NONE})
                end
          | munchStm (T.MOVE ((T.TEMP d), (T.MEM e1))) =
                let val e1' = munchExp e1
                in  emits (OPER {assem = "ldr     `d0, "^(memStr e1 e1'), dest = [d], src = [e1'], jump = NONE})
                end
          | munchStm (T.MOVE ((T.TEMP d), (T.CALL (ename, eargs)))) =
                let val _ = munchStm (T.EXP(T.CALL (ename, eargs)))
                in  emits (MOVE {assem = "movs    `d0, `s0", dest = [d], src = [Tigerframe.rv]})
                end
          | munchStm (T.MOVE ((T.TEMP d), (T.ESEQ (s1, e1)))) =
                let val _ = munchStm s1
                    val e1' = munchExp e1
                in  emits (MOVE {assem = "movs    `d0, `s0", dest = [d], src = [e1']})
                end
          | munchStm (T.MOVE ((T.BINOP _), _)) = raise Fail "MOVE dest = BINOP"
          | munchStm (T.MOVE ((T.MEM e1), e2)) =
                let val (e1', e2') = (munchExp e1, munchExp e2)
                in  emits (OPER {assem = "str     `d0, "^(memStr e1 e1'), dest = [e2'], src = [e1'], jump = NONE})
                end
          | munchStm (T.MOVE ((T.CALL _), _)) = raise Fail "MOVE dest = CALL"
          | munchStm (T.MOVE ((T.ESEQ (s1, e1), e2))) =
                let val _ = munchStm s1
                in  munchStm (T.MOVE (e1, e2))
                end
          | munchStm (T.EXP e1) =
                (munchExp e1; ())
          | munchStm (T.JUMP (e1, llst)) =
                (*let val e1' = munchExp e1*)
                emits (OPER {assem = "b       `j0", dest = [], src = [], jump = SOME llst})
          | munchStm (T.CJUMP (op1, e1, e2, l1, l2)) =
                let val (e1', e2') = (munchExp e1, munchExp e2)
                    val cond = case op1 of
                                    T.EQ => "eq"
                                  | T.NE => "ne"
                                  | T.LT => "lt"
                                  | T.GT => "gt"
                                  | T.LE => "le"
                                  | T.GE => "ge"
                                  | T.ULT => "lo"
                                  | T.ULE => "ls"
                                  | T.UGT => "hi"
                                  | T.UGE => "hs"
                    in  emits (OPER {assem = "b"^cond^"     `j0", dest = [], src = [], jump = SOME [l1, "FALSE_LABEL"]});
                        emits (OPER {assem = "b       `j0", dest = [], src = [], jump = SOME [l2]})
                    end
          | munchStm (T.SEQ (s1, s2)) =
                (munchStm s1; munchStm s2)
          | munchStm (T.LABEL l) =
                emits (LABEL {assem = l^":", lab = l})
        
        and munchBlockLabel x =
                case x of
                     T.LABEL l => emits (LABEL {assem = (Tigerframe.name frame)^":", lab = (Tigerframe.name frame)})
                   | _ => raise Fail "Tigerassem: Bloque básico no empieza con un LABEL"

        and munchExp (T.CONST i) = 
                result (fn x => munchStm (T.MOVE (T.TEMP x, T.CONST i)))
          | munchExp (T.NAME l) = l
          | munchExp (T.TEMP t) = t
          | munchExp (T.BINOP (op1, e1, e2)) =
                result (fn x => munchStm (T.MOVE (T.TEMP x, T.BINOP (op1, e1, e2))))
          | munchExp (T.MEM e1) = munchExp e1
          | munchExp (T.CALL (ename, eargs)) =
                let val len = List.length eargs
                    val ename' = munchExp ename
                    fun str y = T.BINOP (T.PLUS, T.TEMP Tigerframe.sp, T.CONST((y-Tigerframe.argregslen)*Tigerframe.wSz))
                    val indexes = List.tabulate (len, (fn x => x))
                    val eargs' = ListPair.zip(eargs, indexes)
                    fun aux (x,y) = if y < Tigerframe.argregslen then munchStm (T.MOVE (T.TEMP (List.nth((Tigerframe.argregs), y)), x))
                                             else munchStm (T.MOVE ((T.MEM (str y)), x))
                    val _ = if len < Tigerframe.argregslen then () else munchStm (T.MOVE(T.TEMP Tigerframe.sp, (T.BINOP (T.MINUS, T.TEMP Tigerframe.sp, T.CONST((len - Tigerframe.argregslen)*Tigerframe.wSz)))))
                    val eargs'' = List.map aux eargs'
                    val _ = emits (OPER {assem = "bl      `j0", dest = [], src = [], jump = SOME [ename', CALL_LABEL]})
                in Tigerframe.rv
                end
          | munchExp _ = raise Fail "munchExp undefined"

    in
        (ilist := [];
        munchBlockLabel (hd ss);
        List.map munchStm (tl ss);
        !ilist)
    end

end
