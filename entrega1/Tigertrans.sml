structure Tigertrans :> Tigertrans = struct

open Tigerframe
open Tigertree
open Tigertemp
open Tigerabs

exception breakexc
exception divCero
    
type level = {parent:frame option , frame: frame, levelint: int}

fun printLevel (level:level) =
    let val _ = print "\n"
        val _ = case (#parent level) of
                     SOME f => (print "parentFrame = " ; printFrame f)
                   | NONE => print "parent = NONE"
        val _ = print "\n"
        val _ = (print "frame = " ; Tigerframe.printFrame (#frame level))
        val _ = print "\n"
        val _ = (print "levelint = " ; print (Int.toString (#levelint level)))
        val _ = print "\n"
    in () end

type access = Tigerframe.access

type frag = Tigerframe.frag
val fraglist = ref ([]: frag list)

val debug = (fn x => print ("\n\n\nDEBUGTRANS: " ^ x ^ "\n\n\n"))

val actualLevel = ref ~1 (* _Tigermain debe tener level = 0. *)

fun getActualLev() = !actualLevel

val outermost: level = {parent=NONE,
                        frame=newFrame{name="_Tigermain", formals=[]},
                        levelint=getActualLev()}

fun newLevel{parent={parent, frame, levelint}, name, formals} =
    {parent=SOME frame,
     frame=newFrame{name=name, formals=formals},
     levelint=levelint+1}

fun allocArg{parent, frame, levelint} b = Tigerframe.allocArg frame b
fun allocLocal{parent, frame, levelint} b = Tigerframe.allocLocal frame b

fun formals{parent, frame, levelint} = Tigerframe.formals frame

datatype exp =
    Ex of Tigertree.exp
  | Nx of Tigertree.stm
  | Cx of label * label -> Tigertree.stm

fun seq [] = EXP (CONST 0)
  | seq [s] = s
  | seq (x::xs) = SEQ (x, seq xs)

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

fun Ir(e) =
    let fun aux(Ex e) = Tigerit.tree(EXP e)
          | aux(Nx s) = Tigerit.tree(s)
          | aux _ = raise Fail "bueno, a completar!"
        fun aux2(PROC{body, frame}) = aux(Nx body)
          | aux2(STRING(l, "")) = l^":\n"
          | aux2(STRING("", s)) = "\t"^s^"\n"
          | aux2(STRING(l, s)) = l^":\t"^s^"\n"
        fun aux3 [] = ""
          | aux3(h::t) = (aux2 h)^(aux3 t)
    in  aux3 e end

fun nombreFrame frame = print(".globl " ^ Tigerframe.name frame ^ "\n")

(* While y for necesitan la ultima etiqueta para un break *)
local
    val salidas: label option Tigerpila.Pila = Tigerpila.nuevaPila1 NONE
in
    val pushSalida = Tigerpila.pushPila salidas
    fun popSalida() = Tigerpila.popPila salidas
    fun topSalida() =
        case Tigerpila.topPila salidas of
            SOME l => l
          | NONE => raise Fail "break incorrecto!"            
end

val datosGlobs = ref ([]: frag list)

fun procEntryExit{level: level, body} =
    let val label = STRING(name(#frame level), "")
        val body' = PROC{frame= #frame level, body=unNx body}
        val final = STRING(";;-------", "")
    in  datosGlobs:=(!datosGlobs@[label, body', final]) end

fun getResult() = !datosGlobs

fun stringLen s =
    let fun aux[] = 0
          | aux(#"\\":: #"x"::_::_::t) = 1+aux(t)
          | aux(_::t) = 1+aux(t)
    in  aux(explode s) end

fun stringExp(s: string) =
    let val l = newlabel()
        val len = ".long "^makestring(stringLen s)
        val str = ".string \""^s^"\""
        val _ = datosGlobs:=(!datosGlobs @ [STRING(l, len), STRING("", str)])
    in  Ex(NAME l) end

fun preFunctionDec(l, n, f) =
    (pushSalida(NONE);
     actualLevel := !actualLevel+1;
     newLevel{formals=f,name=n,parent=l})

fun functionDec(e, l, proc) =
    let val body = if proc then unNx e
                   else MOVE(TEMP rv, unEx e)
        val body' = procEntryExit1(#frame l, body)
        val () = procEntryExit{body=Nx body', level=l}
    in  Ex(CONST 0) end

fun postFunctionDec() =
    (popSalida(); actualLevel := !actualLevel-1)

fun unitExp() = Ex (CONST 0)

fun nilExp() = Ex (CONST 0)

fun intExp i = Ex (CONST i)

fun simpleVar(InFrame i, nivel) =
        let fun aux 0 = TEMP fp
              | aux n = MEM(BINOP(PLUS,
                        CONST fpPrevLev, aux(n-1))) (* ver si es fpPrevLev *)
        in  Ex (MEM(BINOP(PLUS, aux(!actualLevel - nivel), CONST i))) end
  | simpleVar(InReg l, _) =
        Ex (TEMP l) 

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
    in
        Ex( ESEQ(seq[MOVE(TEMP ra, a),
                     MOVE(TEMP ri, i),
                     EXP(externalCall("_checkindex", [TEMP ra, TEMP ri]))],
                MEM(BINOP(PLUS, TEMP ra,
                    BINOP(MUL, TEMP ri, CONST Tigerframe.wSz)))))
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
        Ex (externalCall("allocArray", [s, i]))
    end

fun callExp (name, external, isproc, lev:level, la) = 
    let val nivel = #levelint lev
        fun aux 0 = TEMP fp
          | aux n = MEM(BINOP(PLUS,
                    CONST fpPrevLev, aux(n-1)))
        val fpLev =
            if nivel = getActualLev() 
            then MEM (BINOP (PLUS, CONST fpPrevLev, TEMP fp))
            else
                if (nivel < getActualLev())
                then aux(getActualLev() - nivel)
                else aux 0
        
        fun preparaArgs [] (rt, re) = (rt, re)
          | preparaArgs (h :: t) (rt, re) =
                case h of
                     Ex(CONST n) => preparaArgs t ((CONST n) :: rt, re)
                   | Ex(NAME n) => preparaArgs t ((NAME n) :: rt, re)
                   | Ex(TEMP n) => preparaArgs t ((TEMP n) :: rt, re)
                   | _ => let val temp = newtemp()
                          in  preparaArgs t ((TEMP temp) :: rt,
                                             MOVE( TEMP temp, unEx h) :: re)
                          end
        val (ta, la') = preparaArgs (rev la) ([], [])
        val ta' = if external then ta else fpLev :: ta
    in
        if isproc then
            Nx( seq( la' @ [EXP( CALL( NAME name, ta') ) ] ) )
        else
            let val temp = newtemp()
            in Ex( ESEQ( seq( la' @ [EXP( CALL( NAME name, ta') ), 
                                        MOVE( TEMP temp, TEMP rv)]),
                   TEMP temp))
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
    in  Cx (fn (t, f) => (CJUMP( oper', eleft, eright, t, f)))
    end

fun binOpStrExp {left,oper,right} =
     let val oper' = case oper of
                         EqOp => EQ
                       | NeqOp => NE
                       | _ => raise Fail ("Error interno en binOpStrExp")
        val eleft = unEx left
        val eright = unEx right
        val temp = newtemp()
    in  Cx (fn (t, f) => seq[EXP(externalCall("_stringCompare", [eleft, eright])), (* 0 si son iguales *)
                             MOVE( TEMP temp, TEMP rv),
                             (CJUMP( oper', TEMP temp, CONST 0, t, f))])
    end

end
