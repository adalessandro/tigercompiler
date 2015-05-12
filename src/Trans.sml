structure Trans :> Trans = struct

open Frame
open Tree
open Temp
open Abs
open Tigerextras

exception breakexc
exception divCero
    
type level = {parent:frame option , frame: frame, levelint: int}

type access = Frame.access

type frag = Frame.frag

val datosGlobs = ref ([]: frag list)

val fraglist = ref ([]: frag list)

val actualLevel = ref ~1 (* _tigermain debe tener level = 0. *)

fun getActualLev() = !actualLevel

val outermost : level = {   parent = NONE,
                            frame = newFrame {name="_tigermain", escapes=[]},
                            levelint = getActualLev()
                        }

fun newLevel {parent = {parent, frame, levelint}, name, formals} =
        {   parent = SOME frame,
            frame = newFrame {name=name, escapes=formals},
            levelint = levelint+1}

fun allocArg {parent, frame, levelint} b = Frame.allocArg frame b

fun allocLocal {parent, frame, levelint} b = Frame.allocLocal frame b

fun formals {parent, frame, levelint} = Frame.formals frame

datatype exp =
        Ex of Tree.exp
      | Nx of Tree.stm
      | Cx of label * label -> Tree.stm

fun unEx (Ex e) = e
  | unEx (Nx s) = ESEQ(s, CONST 0)
  | unEx (Cx cf) =
        let
            val r = newtemp()
            val t = newlabel()
            val f = newlabel()
        in
            ESEQ(seq [MOVE(TEMP r, CONST 1),
                cf (t, f),
                LABEL f,
                MOVE(TEMP r, CONST 0),
                LABEL t],
                TEMP r)
        end

fun unNx (Ex e) = EXP e
  | unNx (Nx s) = s
  | unNx (Cx cf) =
        let
            val t = newlabel()
            val f = newlabel()
        in
            seq [cf(t,f),
                LABEL t,
                LABEL f]
        end

fun unCx (Nx s) = raise Fail ("Error (UnCx(Nx..))")
  | unCx (Cx cf) = cf
  | unCx (Ex (CONST 0)) =
        (fn (t,f) => JUMP(NAME f, [f]))
  | unCx (Ex (CONST _)) =
        (fn (t,f) => JUMP(NAME t, [t]))
  | unCx (Ex e) =
        (fn (t,f) => CJUMP(NE, e, CONST 0, t, f))

(* While y for necesitan la ultima etiqueta para un break *)
local
    val salidas: label option Pila.Pila = Pila.nuevaPila1 NONE
in
    val pushSalida = Pila.pushPila salidas
    fun popSalida() = Pila.popPila salidas
    fun topSalida() =
        case Pila.topPila salidas of
            SOME l => l
          | NONE => raise Fail "break incorrecto!"            
end

fun procEntryExit {level: level, body} =
        let (*val label = STRING (name (#frame level), "")*) (* omitimos agregar el fun label *)
            val body' = PROC {frame = #frame level, body = unNx body}
        in
            datosGlobs := (!datosGlobs @ [body'])
        end

fun getResult() = !datosGlobs

fun stringLen s =
    let fun aux[] = 0
          | aux(#"\\":: #"x"::_::_::t) = 1+aux(t)
          | aux(_::t) = 1+aux(t)
    in  aux(explode s) end

fun stringExp(s: string) =
            let val l = newlabel()
                val len = ".long " ^ makestring(stringLen s)
                val str = ".ascii \"" ^ s ^ "\""
                val _ = datosGlobs:=(!datosGlobs @ [STRING(l, len), STRING("", str)])
            in
                Ex (NAME l)
            end

(* Se crea el level y se inserta en venv antes de recorrer el cuerpo de la función *)
fun initLevelFunctionDec(l, n, f) =
        newLevel {formals=f, name=n, parent=l}

fun preFunctionDec() = (
        pushSalida(NONE);
        actualLevel := (!actualLevel) + 1
    )

fun functionDec(e, l, proc) =
        let val body =
                    if proc then
                        unNx e
                    else
                        MOVE (TEMP rv, unEx e)
            val body' = procEntryExit1 (#frame l, body)
            val _ = procEntryExit {body = Nx body', level = l}
        in
            Ex(CONST 0)
        end

fun postFunctionDec() = (
        popSalida();
        actualLevel := (!actualLevel)-1
    )

fun unitExp() = Ex (CONST 0)

fun nilExp() = Ex (CONST 0)

fun intExp i = Ex (CONST i)

fun simpleVar (InFrame i, nivel) =
        let fun aux 0 = TEMP fp
              | aux n = MEM(BINOP(PLUS,
                            CONST fpPrevLev, aux(n-1)))
        in
            if i = 0 then
                Ex (MEM (aux (!actualLevel - nivel)))
            else if i > 0 then
                Ex (MEM (BINOP (PLUS, aux(!actualLevel-nivel), CONST i)))
            else
                Ex (MEM (BINOP (MINUS, aux(!actualLevel-nivel), CONST (~i))))
        end
  | simpleVar(InReg l, _) = Ex (TEMP l) 

(*fun varDec(acc) = simpleVar(acc, getActualLev())*)
fun varDec(acc, e) = let val sv = unEx (simpleVar(acc, getActualLev()))
                         val ex = unEx e
                     in  Nx (MOVE (sv, ex))
                     end

fun fieldVar(var, pos) = 
    let val t = newtemp()
    in  Ex( ESEQ( seq[MOVE( TEMP t, unEx var),
                      EXP( externalCall("_checkNil", [TEMP t])) ],
                  MEM (BINOP( PLUS, CONST(wSz * pos), TEMP t))))
    end

fun subscriptVar(arr, ind) =
    let
        val a = unEx arr
        val i = unEx ind
        val ra = newtemp()
        val ri = newtemp()
        val ret = newtemp()
    in
        Ex( ESEQ(seq[MOVE(TEMP ra, a),
                     MOVE(TEMP ri, i),
                     EXP(externalCall("_checkIndexArray", [TEMP ra, TEMP ri])),
                     MOVE(TEMP ret, MEM( BINOP(PLUS, TEMP ra,
                                               BINOP(MUL, TEMP ri, CONST Frame.wSz)
                                              )))
                    ],
                TEMP ret)
            )
    end

fun recordExp l =
    let val ret = newtemp()
        fun gentemps 0 = []
          | gentemps n = newtemp() :: gentemps(n-1)
        val regs = gentemps (length l)
        fun aux ((e, s), t) = (MOVE (TEMP t, unEx e), s, TEMP t)
        val lexps = map aux (ListPair.zip (l, regs))
        val l' = Listsort.sort (fn((_, m, _), (_, n, _)) => Int.compare(m, n)) lexps
        val lexps' = map #1 lexps
    in
        Ex( ESEQ( seq( lexps' @ [EXP (externalCall("_allocRecord", CONST (length l) :: (List.map #3 l'))), MOVE ( TEMP ret, TEMP rv) ] ), TEMP ret))
    end
        
fun arrayExp{size, init} =
    let
        val s = unEx size
        val i = unEx init
    in
        Ex (externalCall("_allocArray", [s, i]))
    end

fun callExp (name, external, isproc, lev:level, la) = 
        let (* Get the SL to be passed as an argument *)
            val callerlev = getActualLev()
            val calleelev = #levelint lev
            fun get_sl n = (* n is the number of levels to go up *)
                    if n < 0 then
                        TEMP fp
                    else
                        MEM (BINOP (PLUS, CONST fpPrevLev, get_sl(n-1)))
            val t1 = newtemp()
            val sl = ESEQ (seq [MOVE (TEMP t1, get_sl (callerlev - calleelev))], TEMP t1)

            fun preparaArgs (h, (rt, re)) =
                    case h of
                    Ex(CONST n) => ((CONST n) :: rt, re)
                  | Ex(TEMP n) => ((TEMP n) :: rt, re)
                  | _ => let val temp = newtemp()
                         in
                            ((TEMP temp) :: rt, MOVE (TEMP temp, unEx h) :: re)
                         end
            val (ta, la') = List.foldl preparaArgs ([], []) la
            val ta' = if external then ta else sl :: ta
            val argsAndCall = la' @ [EXP(CALL(NAME name, ta'))]
        in
            if isproc then
                Nx (seq argsAndCall)
            else
                let val t2 = newtemp()
                in
                    Ex (ESEQ (seq (argsAndCall @ [MOVE(TEMP t2, TEMP rv)]), TEMP t2))
                end
        end

fun letExp ([], body) = Ex (unEx body)
 |  letExp (inits, body) = Ex (ESEQ(seq inits,unEx body))

fun breakExp() = 
    let val ts = topSalida()
    in  Nx (seq[JUMP(NAME ts, [ts])]) end

fun seqExp ([]:exp list) = Nx (EXP(CONST 0))
    | seqExp (exps:exp list) =
        let
            fun unx [e] = []
                | unx (s::ss) = (unNx s)::(unx ss)
                | unx[] = []
        in
            case List.last exps of
                Nx s =>
                    let val unexps = map unNx exps
                    in Nx (seq unexps) end
                | Ex e => Ex (ESEQ(seq(unx exps), e))
                | cond => Ex (ESEQ(seq(unx exps), unEx cond))
        end

fun preWhileForExp() = pushSalida(SOME(newlabel()))

fun postWhileForExp() = (popSalida(); ())

fun whileExp {test: exp, body: exp, lev:level} =
    let
        val cf = unCx test
        val expb = unNx body
        val (l1, l2, l3) = (newlabel(), newlabel(), topSalida())
    in
        Nx (seq[LABEL l1,
            cf(l2,l3),
            LABEL l2,
            expb,
            JUMP(NAME l1, [l1]),
            LABEL l3])
    end

fun forExp {lo, hi, var, body} =
    let
        val inf = unEx lo
        val sup = unEx hi
        val expBody = unNx body
        val (l1, l2, l3) = (newlabel(), topSalida(), newlabel())
        val (r1, r2) = (newtemp(), newtemp())
        val expVar = unEx var
    in
        Nx (seq[MOVE(expVar, inf),
                MOVE(TEMP r1, inf),
                MOVE(TEMP r2, sup),
                LABEL l1,
                CJUMP(GT, expVar, TEMP r2, l2, l3),
                LABEL l3,
                expBody,
                MOVE(expVar, BINOP(PLUS, (CONST 1), expVar)),
                JUMP(NAME l1, [l1]),
                LABEL l2])
    end

fun ifThenExp{test, then'} =
    let
        val cTest = unCx test
        val nThen = unNx then'
        val (l1, l2) = (newlabel(), newlabel())
    in
        Nx (seq[cTest(l1, l2),
                LABEL l1,
                nThen,
                LABEL l2])
    end

fun ifThenElseExp {test, then', else'} =
    let
        val cTest = unCx test
        val eThen = unEx then'
        val eElse = unEx else'
        val r1 = newtemp()
        val (l1, l2, l3) = (newlabel(), newlabel(), newlabel())
    in
        Ex (ESEQ((seq[cTest(l1, l2),
                    LABEL l1,
                    MOVE(TEMP r1, eThen),
                    JUMP(NAME l3, [l3]),
                    LABEL l2,
                    MOVE(TEMP r1, eElse),
                    LABEL l3]),
                TEMP r1))
    end

fun ifThenElseExpUnit {test, then', else'} =
    let
        val cTest = unCx test
        val nThen = unNx then'
        val nElse = unNx else'
        val (l1, l2, l3) = (newlabel(), newlabel(), newlabel())
    in
        Nx (seq[cTest(l1, l2),
                LABEL l1,
                JUMP(NAME l3, [l3]),
                nThen,
                LABEL l2,
                nElse,
                LABEL l3])
    end

fun assignExp{var, exp} =
let
    val v = unEx var
    val vl = unEx exp
in
    Nx (MOVE(v,vl))
end

fun binOpIntExp {left, oper, right} = 
    let val oper' = case oper of
                         PlusOp => PLUS
                       | MinusOp => MINUS
                       | TimesOp => MUL
                       | DivideOp => DIV
                       | _ => raise Fail ("Error interno en binOpIntExp")
        val eleft = unEx left
        val eright = unEx right
    in  Ex(BINOP(oper', eleft, eright))
    end

fun binOpIntRelExp {left,oper,right} =
        let val oper' = case oper of
                        LtOp => LT
                      | LeOp => LE
                      | GtOp => GT
                      | GeOp => GE
                      | EqOp => EQ
                      | NeqOp => NE
                      | _ => raise Fail ("Error interno en binOpIntRelExp")
            val eleft = unEx left
            val eright = unEx right
        in
            Cx (fn (t, f) => (CJUMP( oper', eleft, eright, t, f)))
        end

fun binOpStrExp {left,oper,right} =
        let val oper' =
                    case oper of
                    EqOp => EQ
                  | NeqOp => NE
                  | _ => raise Fail ("Error interno en binOpStrExp")
            val eleft = unEx left
            val eright = unEx right
            val temp = newtemp()
        in  Cx (fn (t, f) => seq[EXP(externalCall("_stringCompare", [eleft, eright])), 
                             MOVE(TEMP temp, TEMP rv),
                             (CJUMP(oper', TEMP temp, CONST 0, t, f))])
        end

(* Extras *)
fun printLevel (level:level) = (
        print "\n"; (
            case (#parent level) of
            SOME f => (print "parentFrame = " ; printFrame f)
          | NONE => print "parent = NONE"
        );
        print "\n";
        print "frame = ";
        Frame.printFrame (#frame level);
        print "\n";
        print "levelint = ";
        print (Int.toString (#levelint level));
        print "\n"
    )

end
