structure Assem :> Assem =
struct

structure T = Tree

open Tigerextras

type reg = string
type temp = Temp.temp
type label = Temp.label

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
   
val ilist = ref []
fun emits x = ilist := x :: (!ilist)

val FALSE_LABEL = "__FALSE_LABEL__"
val RET_LABEL = "__RET_LABEL__"
val CALL_LABEL = "__CALL_LABEL__" 

fun const i = "#" ^ Int.toString(i)
fun flabel l = "=" ^ l

fun result gen = 
        let val t = Temp.newtemp()
        in 
            gen t; t
        end

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
                if d = Frame.pc andalso s = Frame.lr
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
                in  emits (MOVE {assem = "movs    `d0, `s0", dest = [d], src = [Frame.rv]})
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
                in  emits (MOVE {assem = "movs    `d0, `s0", dest = [d], src = [Frame.rv]})
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
                    in  emits (OPER {assem = "cmp     `s0, `s1", dest = [], src = [e1', e2'], jump = NONE});
                        emits (OPER {assem = "b"^cond^"     `j0", dest = [], src = [], jump = SOME [l1, FALSE_LABEL]});
                        emits (OPER {assem = "b       `j0", dest = [], src = [], jump = SOME [l2]})
                    end
          | munchStm (T.SEQ (s1, s2)) =
                (munchStm s1; munchStm s2)
          | munchStm (T.LABEL l) =
                emits (LABEL {assem = l^":", lab = l})
        
        and munchBlockLabel x =
                case x of
                     T.LABEL l => emits (LABEL {assem = (Frame.name frame)^":", lab = (Frame.name frame)})
                   | _ => raise Fail "Assem: Bloque básico no empieza con un LABEL"

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
                    fun str y = T.BINOP (T.PLUS, T.TEMP Frame.sp, T.CONST((y-Frame.argregslen)*Frame.wSz))
                    val indexes = List.tabulate (len, (fn x => x))
                    val eargs' = ListPair.zip(eargs, indexes)
                    fun aux (x,y) = if y < Frame.argregslen then munchStm (T.MOVE (T.TEMP (List.nth((Frame.argregs), y)), x))
                                             else munchStm (T.MOVE ((T.MEM (str y)), x))
                    val _ = if len < Frame.argregslen then () else munchStm (T.MOVE(T.TEMP Frame.sp, (T.BINOP (T.MINUS, T.TEMP Frame.sp, T.CONST((len - Frame.argregslen)*Frame.wSz)))))
                    val eargs'' = List.map aux eargs'
                    val _ = emits (OPER {assem = "bl      `j0", dest = [], src = [], jump = SOME [ename', CALL_LABEL]})
                in Frame.rv
                end
          | munchExp _ = raise Fail "munchExp undefined"

    in
        ilist := [];
        munchBlockLabel (hd ss);
        List.map munchStm (tl ss);
        !ilist
    end


(* ----- Extras ----- *)
fun getTemps instr =
        case instr of
        OPER {dest = dest, src = src, ...} => dest @ src
      | LABEL _ => []
      | MOVE {dest = dest, src = src, ...} => dest @ src

fun labelpos x [] = raise Fail "labelpos: label not found"
  | labelpos x (LABEL {lab=lab, ...} :: ys) =
            if lab = x then 0 else 1 + labelpos x ys
  | labelpos x (_ :: ys) = 1 + labelpos x ys

val format =
    let fun speak(assem, dst, src, jump) =
            let fun get_elem ls i = List.nth (ls, ord i - ord #"0")
                fun saylab s = s 
                fun saytemp t = t 
                fun f(#"`" :: #"s" :: i ::rest) = 
                        (saytemp o get_elem src) i ^ f rest
                  | f( #"`":: #"d":: i:: rest) = 
                        (saytemp o get_elem dst) i ^ f rest
                  | f( #"`":: #"j":: i:: rest) = 
                        (saylab o get_elem jump) i ^ f rest
                  | f( #"`":: _ :: rest) = raise Fail "bad Assem format"
                  | f(c :: rest) = (str c ^ f rest)
                  | f nil = "" 
            in (f o explode) assem
            end 
    in fn OPER {assem, dest, src, jump=NONE} => speak("\t" ^ assem, dest, src, nil)
        | OPER {assem, dest, src, jump=SOME j} => speak("\t" ^ assem, dest, src, j)
        | LABEL {assem, ...} => assem
        | MOVE {assem, dest, src} => speak("\t" ^ assem, dest, src, nil)
    end

fun strAssem i = format i ^ "\n"

fun printAssem i = (print o strAssem) i

(* Reemplazar las ocurrencias del temp t por el registro r en una instrucción. *)
fun replace (t, r) =
        let fun rep ls = List.map (fn x => if x = t then r else x) ls
        in
            fn OPER {assem=a, dest=d, src=s, jump=j} => OPER {assem=a, dest=rep d, src=rep s, jump=j}
             | LABEL {assem=a, lab=l} => LABEL {assem=a, lab=l}
             | MOVE {assem=a, dest=d, src=s} => MOVE {assem=a, dest=rep d, src=rep s}
        end

end
