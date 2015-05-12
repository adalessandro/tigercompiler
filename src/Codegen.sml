structure Codegen :> Codegen =
struct

structure T = Tree

open Tigerextras
open Assem

val ilist = ref []
fun emits x = ilist := x :: (!ilist)

fun memStr x e1' =
        case x of
        (T.CONST _) => e1'
      | (T.NAME _) => e1'
      | (T.TEMP _) => "[`s0]"
      | (T.BINOP _) => "[`s0]"
      | (T.ESEQ (st, ex)) => memStr ex e1'
      | _ => raise Fail "memStr undefined"

fun result gen = 
        let val t = Temp.newtemp()
        in 
            gen t; t
        end

(* global stuff *)
val gblframes : Frame.frame list ref = ref []

fun getframe name : Frame.frame option = List.find (fn f => Frame.name f = name) (!gblframes)

(* Codegen functions *)
fun munchStmBlock (ss, frame) = 
        let fun munchStm (T.MOVE ((T.CONST _), _)) = raise Fail "MOVE dest = CONST"
              | munchStm (T.MOVE ((T.NAME _), _)) = raise Fail "MOVE dest = NAME"
              | munchStm (T.MOVE ((T.TEMP d), (T.CONST i))) = 
                        emits (OPER {assem = "mov     `d0, " ^ Assem.const(i),
                                     dest = [d], src = [], jump = NONE})
              | munchStm (T.MOVE ((T.TEMP d), (T.NAME l))) =
                        emits (OPER {assem = "ldr     `d0, " ^ Assem.flabel(l),
                                     dest = [d], src = [], jump = NONE})
              | munchStm (T.MOVE ((T.TEMP d), (T.TEMP s))) =
                        emits (MOVE {assem = "mov    `d0, `s0", dest = [d], src = [s]})
              | munchStm (T.MOVE ((T.TEMP d), (T.BINOP (T.PLUS, e1, e2)))) =
                        let val (e1', e2') = (munchExp e1, munchExp e2)
                        in
                            emits (OPER {assem = "add    `d0, `s0, `s1",
                                         dest = [d], src = [e1', e2'], jump = NONE})
                        end
              | munchStm (T.MOVE ((T.TEMP d), (T.BINOP (T.MUL, e1, e2)))) =
                        let val (e1', e2') = (munchExp e1, munchExp e2)
                            val (e1'', e2'') = if (d = e1') then (e2', e1') else (e1', e2')
                        in
                            emits (OPER {assem = "mul    `d0, `s0, `s1",
                                         dest = [d], src = [e1'', e2''], jump = NONE})
                        end
              | munchStm (T.MOVE ((T.TEMP d), (T.BINOP (T.MINUS, e1, e2)))) =
                        let val (e1', e2') = (munchExp e1, munchExp e2)
                        in
                            emits (OPER {assem = "sub    `d0, `s0, `s1",
                                         dest = [d], src = [e1', e2'], jump = NONE})
                        end
              | munchStm (T.MOVE ((T.TEMP d), (T.BINOP (T.DIV, e1, e2)))) = (
                        munchStm (T.EXP (T.CALL (T.NAME "idiv", [e1, e2])));
                        emits (MOVE {assem = "mov     `d0, `s0", dest = [d], src = [Frame.rv]})
                    )
              | munchStm (T.MOVE ((T.TEMP d), (T.BINOP (T.AND, e1, e2)))) =
                        let val (e1', e2') = (munchExp e1, munchExp e2)
                        in
                            emits (OPER {assem = "and    `d0, `s0, `s1",
                                         dest = [d], src = [e1', e2'], jump = NONE})
                        end
              | munchStm (T.MOVE ((T.TEMP d), (T.BINOP (T.OR, e1, e2)))) =
                        let val (e1', e2') = (munchExp e1, munchExp e2)
                        in
                            emits (OPER {assem = "orr    `d0, `s0, `s1",
                                         dest = [d], src = [e1', e2'], jump = NONE})
                        end
              | munchStm (T.MOVE ((T.TEMP d), (T.BINOP (T.XOR, e1, e2)))) =
                        let val (e1', e2') = (munchExp e1, munchExp e2)
                        in
                            emits (OPER {assem = "eor    `d0, `s0, `s1",
                                         dest = [d], src = [e1', e2'], jump = NONE})
                        end
              | munchStm (T.MOVE ((T.TEMP d), (T.BINOP (T.LSHIFT, e1, e2)))) =
                        let val (e1', e2') = (munchExp e1, munchExp e2)
                        in
                            emits (OPER {assem = "mov    `d0, `s0, lsl `s1",
                                         dest = [d], src = [e1', e2'], jump = NONE})
                        end
              | munchStm (T.MOVE ((T.TEMP d), (T.BINOP (T.RSHIFT, e1, e2)))) =
                        let val (e1', e2') = (munchExp e1, munchExp e2)
                        in
                            emits (OPER {assem = "mov    `d0, `s0, lsr `s1",
                                         dest = [d], src = [e1', e2'], jump = NONE})
                        end
              | munchStm (T.MOVE ((T.TEMP d), (T.BINOP (T.ARSHIFT, e1, e2)))) =
                        let val (e1', e2') = (munchExp e1, munchExp e2)
                        in
                            emits (OPER {assem = "mov    `d0, `s0, asr `s1",
                                         dest = [d], src = [e1', e2'], jump = NONE})
                        end
              | munchStm (T.MOVE ((T.TEMP d), (T.MEM e1))) =
                        let val e1' = munchExp e1
                        in
                            emits (OPER {assem = "ldr     `d0, " ^ (memStr e1 e1'),
                                         dest = [d], src = [e1'], jump = NONE})
                        end
              | munchStm (T.MOVE ((T.TEMP d), (T.CALL (ename, eargs)))) = (
                        munchStm (T.EXP(T.CALL (ename, eargs)));
                        emits (MOVE {assem = "mov    `d0, `s0", dest = [d], src = [Frame.rv]})
                    )
              | munchStm (T.MOVE ((T.TEMP d), (T.ESEQ (s1, e1)))) =
                        let val _ = munchStm s1
                            val e1' = munchExp e1
                        in
                            emits (MOVE {assem = "mov    `d0, `s0", dest = [d], src = [e1']})
                        end
              | munchStm (T.MOVE ((T.BINOP _), _)) = raise Fail "MOVE dest = BINOP"
              | munchStm (T.MOVE ((T.MEM e1), e2)) =
                        let val (e1', e2') = (munchExp e1, munchExp e2)
                        in
                            emits (OPER {assem = "str     `s1, " ^ (memStr e1 e1'),
                                         dest = [], src = [e1', e2'], jump = NONE})
                        end
              | munchStm (T.MOVE ((T.CALL _), _)) = raise Fail "MOVE dest = CALL"
              | munchStm (T.MOVE ((T.ESEQ (s1, e1), e2))) = (
                        munchStm s1;
                        munchStm (T.MOVE (e1, e2))
                    )
              | munchStm (T.EXP e1) = (munchExp e1; ())
              | munchStm (T.JUMP (e1, llst)) = (
                        emits (OPER {assem = "b       `j0",
                                     dest = [], src = [], jump = SOME llst})
                )
              | munchStm (T.CJUMP (op1, e1, e2, l1, l2)) =
                        let val (e1', e2') = (munchExp e1, munchExp e2)
                            val cond =
                                    case op1 of
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
                            in
                                emits (OPER {assem = "cmp     `s0, `s1",
                                             dest = [], src = [e1', e2'], jump = NONE});
                                emits (OPER {assem = "b" ^ cond ^ "     `j0",
                                             dest = [], src = [], jump = SOME [l1, FALSE_LABEL]});
                                emits (OPER {assem = "b       `j0",
                                             dest = [], src = [], jump = SOME [l2]})
                            end
              | munchStm (T.SEQ (s1, s2)) = (munchStm s1; munchStm s2)
              | munchStm (T.LABEL l) = emits (LABEL {assem = l ^ ":", lab = l})
            
            and munchArgStack (arg, pos) =
                    let val memdir = pos * Frame.wSz
                        val e = munchExp arg
                    in
                            emits (OPER {assem = "str     `s0, [sp, " ^ Assem.const(memdir) ^ "]",
                                         src = [e], dest = [], jump = NONE});
                            pos + 1
                    end

            and munchArgReg (T.TEMP t, reg) = (
                        munchStm (T.MOVE (T.TEMP reg, T.TEMP t));
                        [t, reg]
                    )
              | munchArgReg (e, reg) =
                    let val e' = munchExp e
                    in
                        munchStm (T.MOVE (T.TEMP reg, T.TEMP e'));
                        [e', reg]
                    end

            and munchExp (T.CONST i) = result (fn x => munchStm (T.MOVE (T.TEMP x, T.CONST i)))
              | munchExp (T.NAME l) = l
              | munchExp (T.TEMP t) = t
              | munchExp (T.BINOP (op1, e1, e2)) =
                        result (fn x => munchStm (T.MOVE (T.TEMP x, T.BINOP (op1, e1, e2))))
              | munchExp (T.MEM e1) =
                        result (fn x => munchStm (T.MOVE (T.TEMP x, T.MEM e1)))
              | munchExp (T.CALL (ename, eargs)) =
                        let val ename' = munchExp ename
                            val frm = getframe ename'
                            val (toreg, toframe) = (
                                    case frm of
                                    NONE => (* external call *)
                                            if List.length eargs <= Frame.argregslen then
                                                (eargs, [])
                                            else
                                                (List.take (eargs, Frame.argregslen),
                                                 List.drop (eargs, Frame.argregslen))
                                  | SOME frm' => (* internal call *)
                                            let val formals =
                                                        Frame.InReg "SL" :: (Frame.formals frm')
                                                val zip = ListPair.zip (eargs, formals)
                                                val (argsreg, argsframe) =
                                                        List.partition (Frame.isInReg o #2) zip
                                            in
                                                (List.map #1 argsreg, List.map #1 argsframe)
                                            end
                                )
                            val sp_offset = (List.length toframe) * Frame.wSz
                            val toreg_zip = ListPair.zip (toreg, Frame.argregs)
                            val result_t = Temp.newtemp()
                            val _ = if sp_offset <> 0 then
                                        emits (OPER {assem = "sub     sp, sp, " ^
                                                              Assem.const(sp_offset),
                                                     src = [], dest = [], jump = NONE})
                                    else ()
                            val _ = List.foldl munchArgStack 0 toframe
                            val srcs = List.concat (List.map munchArgReg toreg_zip)
                            val _ = emits (OPER {assem = "bl      `j0",
                                                 dest = (*result_t :: *)Frame.callersaves,
                                                 src = [] (*srcs*),
                                                 jump = SOME [ename', CALL_LABEL]})
                            val _ = if sp_offset <> 0 then
                                        emits (OPER {assem = "add     sp, sp, " ^
                                                              Assem.const(sp_offset),
                                                     src = [], dest = [], jump = NONE})
                                    else ()
                            val _ = munchStm (T.MOVE (T.TEMP result_t, T.TEMP Frame.rv))
                        in
                            result_t
                        end
              | munchExp _ = raise Fail "munchExp undefined"

            and getBlockLabel x =
                    case x of
                    T.LABEL l => (LABEL {assem = (Frame.name frame) ^ ":",
                                         lab = (Frame.name frame)})
                  | _ => raise Fail "Assem: Bloque básico no empieza con un LABEL"

        in
            ilist := []; (* reset global list *)
            List.map munchStm (tl ss); (* generate body *)
            getBlockLabel (hd ss) :: (* generate function label *)
                Frame.procEntryExit2 (frame, List.rev(!ilist)) (* generate sink instr *)
        end

(* Main function *)
fun codegen (blocks : (Tree.stm list * Frame.frame) list) =
        let val _ = gblframes := (List.map #2 blocks)
        in
            List.map munchStmBlock blocks
        end

(* Reemplazar las ocurrencias del temp t por el registro r en una instrucción. *)
fun safeSubstring (s, i, n) =
        String.substring (s, i, n)
        handle Subscript => ""
        
val checkSpecialCases =
        let
        in
            fn OPER {assem=a, dest=d, src=s, jump=j} => (
                        case (safeSubstring (a, 0, 4)) of
                        "mul " => (* El mundo explotará si el dest y los dos src son el mismo *)
                                if List.hd d = List.hd s then
                                    OPER {assem=a, dest=d, src=List.rev s, jump=j}
                                else
                                    OPER {assem=a, dest=d, src=s, jump=j}
                      | _ => OPER {assem=a, dest=d, src=s, jump=j}
                    )
             | x => x
        end

fun replace (t, r) =
        let fun rep ls = List.map (fn x => if x = t then r else x) ls
        in
            fn OPER {assem=a, dest=d, src=s, jump=j} =>
                        checkSpecialCases (OPER {assem=a, dest=rep d, src=rep s, jump=j})
             | LABEL {assem=a, lab=l} => LABEL {assem=a, lab=l}
             | MOVE {assem=a, dest=d, src=s} => MOVE {assem=a, dest=rep d, src=rep s}
        end

end
