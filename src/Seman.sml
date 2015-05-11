structure Seman :> Seman =
struct

open Abs
open Sres
open Topsort
open Trans
open Tigerextras

(* Pilas para el manejo de levels de anidamiento de funciones *)
val levelPila: Trans.level Pila.Pila = Pila.nuevaPila1(Trans.outermost) 
fun pushLevel l = Pila.pushPila levelPila l
fun popLevel() = Pila.popPila levelPila 
fun topLevel() = Pila.topPila levelPila

(* label gen temporal *)
local
    val n = ref 0
in
    fun newLabel() = !n before n:= !n + 1
end

(* Tipo tabla espacio de nombres de variables y funciones *)
type venv = (string, EnvEntry) Tab.Tabla

(* Tipo tabla espacio de nombres de tipos *)
type tenv = (string, Tipo) Tab.Tabla

fun printtenv tenv = map (fn x => print (("("^(#1 x)^", "^printTipo(#2 x)^")")^"\n")) (tabAList tenv)

fun printvenv venv = map (fn x => print (("("^(#1 x)^", "^envEntry2String(#2 x)^")")^"\n")) (tabAList venv)

fun varName (SimpleVar s) = s
  | varName (FieldVar (v, _)) = varName v
  | varName (SubscriptVar (v, _)) = varName v

(* Tabla inicial del espacio de nombres de variables y funciones *)
val tab_vars : (string, EnvEntry) Tabla = tabInserList(
    tabNueva(),
    [("print", Func{level=topLevel(), label="print",
        formals=[TString], result=TUnit, extern=true}),
    ("flush", Func{level=topLevel(), label="flush",
        formals=[], result=TUnit, extern=true}),
    ("getchar", Func{level=topLevel(), label="getstr",
        formals=[], result=TString, extern=true}),
    ("ord", Func{level=topLevel(), label="ord",
        formals=[TString], result=TInt RW, extern=true}),
    ("chr", Func{level=topLevel(), label="chr",
        formals=[TInt RW], result=TString, extern=true}),
    ("size", Func{level=topLevel(), label="size",
        formals=[TString], result=TInt RW, extern=true}),
    ("substring", Func{level=topLevel(), label="substring",
        formals=[TString, TInt RW, TInt RW], result=TString, extern=true}),
    ("concat", Func{level=topLevel(), label="concat",
        formals=[TString, TString], result=TString, extern=true}),
    ("not", Func{level=topLevel(), label="not",
        formals=[TInt RW], result=TInt RW, extern=true}),
    ("exit", Func{level=topLevel(), label="exit",
        formals=[TInt RW], result=TUnit, extern=true})
    ])

(* Tabla inicial del espacio de nombres de tipos *)
val tab_tipos : (string, Tipo) Tabla = 
    tabInserList(
        tabNueva(),
        [("int", TInt RW), ("string", TString)]
    )

(* tipoReal: Tips.Tipo -> Tips.Tipo
    Devuelve el tipo original de un sinónimo de tipo *)
fun tipoReal (TTipo (s, ref (SOME (t)))) = tipoReal t
  | tipoReal t = t

(* tiposIguales: Tips.Tipo -> Tips.Tipo -> bool
    Evalúa si 2 expr tiene igual tipo y devuelve un Bool *)
fun tiposIguales (TRecord _) TNil = true
  | tiposIguales TNil (TRecord _) = true
  | tiposIguales (TInt _) (TInt _) = true
  | tiposIguales (TRecord (_, u1)) (TRecord (_, u2 )) = (u1=u2)
  | tiposIguales (TArray (_, u1)) (TArray (_, u2)) = (u1=u2)
  | tiposIguales (TTipo (_, r)) b =
        let val a = case !r of
            SOME t => t
          | NONE => raise Fail "Internal error (1)"
        in  tiposIguales a b
        end
  | tiposIguales a (TTipo (_, r)) =
        let val b = case !r of
            SOME t => t
          | NONE => raise Fail "Internal error (2)"
        in  tiposIguales a b
        end
  | tiposIguales a b = (a=b)

(* transExp: venv -> tenv -> Abs.exp -> 
    Tipa una expr con los entornos venv, tenv. *)
fun transExp(venv, tenv) =
    let fun error(s, p) = raise Fail ("Error -- línea "^Int.toString(p)^": "^s^"\n")
        fun trexp(VarExp v) = trvar(v)
          | trexp(UnitExp _) = {exp=unitExp(), ty=TUnit}
          | trexp(NilExp _) = {exp=nilExp(), ty=TNil}
          | trexp(IntExp(i, _)) = {exp=intExp i, ty=TInt RW}
          | trexp(StringExp(s, _)) = {exp=stringExp(s), ty=TString}
          | trexp(CallExp({func, args}, nl)) = 
                let val (level, label, forms, res, ext) =
                    (* Recuperar la declaración de la función *)
                        case tabBusca(func, venv) of
                            SOME (Func{level, label, formals, result, extern}) =>
                                (level, label, formals, result, extern)
                          | SOME _ => error(func^" no es una función", nl)
                          | NONE => error(func^" no está definido", nl)
                    (* Matcheo args en declaración con los de la llamada *)
                    fun aux [] [] r = r
                      | aux [] _ _ = error("demasiados argumentos", nl)
                      | aux _ [] _ = error("faltan argumentos", nl)
                      | aux (t::tt) (a::aa) r =
                            let val {exp=ae', ty=te'} = trexp a
                                val _ = if not (tiposIguales t te') 
                                        then error("tipos distintos", nl) 
                                        else ()
                            in aux tt aa r@[{exp=ae', ty=te'}]
                            end
                    val leargs = aux forms args []
                    val leargs' = map #exp leargs
                    val pf = (res = TUnit) (* es procedure o función? *)
                in  {exp=callExp(label, ext, pf, level, leargs'), ty=tipoReal(res)}
                end
          | trexp(OpExp({left, oper=EqOp, right}, nl)) =
                let val {exp=expl, ty=tyl} = trexp left
                    val {exp=expr, ty=tyr} = trexp right
                    val exp' = if tiposIguales tyl TString
                               then binOpStrExp {left=expl, oper=EqOp, right=expr}
                               else binOpIntRelExp {left=expl, oper=EqOp, right=expr}
                in  if tiposIguales tyl tyr andalso 
                        not (tyl=TNil andalso tyr=TNil) andalso 
                        tyl<>TUnit 
                    then {exp=exp', ty=TInt RW}
                    else error("Tipos no comparables", nl)
                end
          | trexp(OpExp({left, oper=NeqOp, right}, nl)) = 
                let val {exp=expl, ty=tyl} = trexp left
                    val {exp=expr, ty=tyr} = trexp right
                    val exp' = if tiposIguales tyl TString
                               then binOpStrExp {left=expl, oper=NeqOp, right=expr}
                               else binOpIntRelExp {left=expl, oper=NeqOp, right=expr}
                in  if tiposIguales tyl tyr andalso 
                        not (tyl=TNil andalso tyr=TNil) andalso 
                        tyl<>TUnit 
                    then {exp=exp', ty=TInt RW}
                    else error("Tipos no comparables", nl)
                end
          | trexp(OpExp({left, oper, right}, nl)) = 
                let val {exp=expl, ty=tyl} = trexp left
                    val {exp=expr, ty=tyr} = trexp right
                in  if tiposIguales tyl tyr
                    then case oper of
                        PlusOp => if tiposIguales tyl (TInt RW)
                                  then {exp=binOpIntExp {left=expl, oper=oper, right=expr}, ty=TInt RW}
                                  else error("Error de tipos", nl)
                      | MinusOp => if tiposIguales tyl (TInt RW)
                                   then {exp=binOpIntExp {left=expl, oper=oper, right=expr}, ty=TInt RW}
                                   else error("Error de tipos", nl)
                      | TimesOp => if tiposIguales tyl (TInt RW)
                                   then {exp=binOpIntExp {left=expl, oper=oper, right=expr}, ty=TInt RW} 
                                   else error("Error de tipos", nl)
                      | DivideOp => if tiposIguales tyl (TInt RW)
                                    then {exp=binOpIntExp {left=expl, oper=oper, right=expr}, ty=TInt RW} 
                                    else error("Error de tipos", nl)
                      | LtOp => if tiposIguales tyl (TInt RW) orelse tiposIguales tyl (TString)
                                then {exp=binOpIntRelExp {left=expl, oper=oper, right=expr}, ty=TInt RW} 
                                else error("Error de tipos", nl)
                      | LeOp => if tiposIguales tyl (TInt RW) orelse tiposIguales tyl (TString)
                                then {exp=binOpIntRelExp {left=expl, oper=oper, right=expr}, ty=TInt RW} 
                                else error("Error de tipos", nl)
                      | GtOp => if tiposIguales tyl (TInt RW) orelse tiposIguales tyl (TString)
                                then {exp=binOpIntRelExp {left=expl, oper=oper, right=expr}, ty=TInt RW} 
                                else error("Error de tipos", nl)
                      | GeOp => if tiposIguales tyl (TInt RW) orelse tiposIguales tyl (TString) 
                                then {exp=binOpIntRelExp {left=expl, oper=oper, right=expr}, ty=TInt RW} 
                                else error("Error de tipos", nl)
                      | _ => raise Fail "Internal error (3)"
                    else error("Error de tipos", nl)
                end
          | trexp(RecordExp({fields, typ}, nl)) =
                let (* Traducir cada expresión de fields *)
                    val tfields = map (fn (sy,ex) => (sy, trexp ex)) fields
                    (* Buscar el tipo *)
                    val (tyr, cs) = case tabBusca(typ, tenv) of
                        SOME t => (case tipoReal t of
                            TRecord(cs, u) => (TRecord(cs, u), cs)
                          | _ => error(typ^" no es de tipo record", nl))
                      | NONE => error("Tipo inexistente ("^typ^")", nl)
                    (* Verificar orden de los campos y tipado correspondiente *)
                    fun verificar _ [] [] = []
                      | verificar _ (c::cs) [] = error("Faltan campos", nl)
                      | verificar _ [] (c::cs) = error("Sobran campos", nl)
                      | verificar n ((s,t,_)::cs) ((sy,{exp,ty})::ds) =
                            if s<>sy then error("Error de campo", nl)
                            else if tiposIguales ty t then (exp, n)::(verificar (n+1) cs ds)
                                 else error("Error de tipo del campo "^s, nl)
                    val lf = verificar 0 cs tfields
                in  {exp=recordExp lf, ty=tipoReal(tyr)}
                end
          | trexp(SeqExp(s, nl)) =
                let val lexti = map trexp s
                    val exprs = map #exp lexti
                    val {exp, ty=tipo} = hd(rev lexti)
                in  {exp=seqExp(exprs), ty=tipoReal(tipo)}
                end
          | trexp(AssignExp({var, exp}, nl)) =
                let val {exp=expvar, ty=tyvar} = trvar(var, nl)
                    val {exp=assexp, ty=tyexp} = trexp exp
                in  if tipoReal tyvar = (TInt RO)
                    then error("Variable de solo lectura no puede ser asignada", nl)
                    else if tiposIguales tyvar tyexp
                         then {exp=assignExp{var=expvar, exp=assexp}, ty=TUnit}
                         else error("Los tipos no coinciden en asignación.", nl)
                end
          | trexp(IfExp({test, then', else'=SOME else'}, nl)) =
                let val {exp=testexp, ty=tytest} = trexp test
                    val {exp=thenexp, ty=tythen} = trexp then'
                    val {exp=elseexp, ty=tyelse} = trexp else'
                    val exp' = if tipoReal tythen = TUnit
                               then ifThenElseExpUnit {test=testexp, then'=thenexp, else' = elseexp}
                               else ifThenElseExp {test=testexp, then'=thenexp, else' = elseexp}
                in  if tipoReal tytest=TInt RW andalso 
                      tiposIguales tythen tyelse 
                    then {exp=exp', ty=tipoReal(tythen)}
                    else error("Error de tipos en if", nl)
                end
          | trexp(IfExp({test, then', else'=NONE}, nl)) =
                let val {exp=exptest, ty=tytest} = trexp test
                    val {exp=expthen, ty=tythen} = trexp then'
                    val exp' = ifThenExp {test=exptest, then'=expthen}
                in if tipoReal tytest=TInt RW andalso tythen=TUnit
                   then {exp=exp', ty=TUnit}
                   else error("Error de tipos en if", nl)
                end
          | trexp(WhileExp({test, body}, nl)) =
                let val ttest = trexp test
                    val _ = preWhileForExp()
                    val tbody = trexp body
                    val exp' = whileExp {test=(#exp ttest), body=(#exp tbody), lev=topLevel()}
                    val _ = postWhileForExp()
                    val _ = if tipoReal(#ty ttest) = TInt RW
                            then ()
                            else error("Error de tipo en la condición", nl)
                    val _ = if #ty tbody = TUnit
                            then ()
                            else error("Cuerpo de while no puede devolver un valor", nl)
                    
                in  {exp=exp', ty=TUnit}
                end
          | trexp(ForExp({var, escape, lo, hi, body}, nl)) = 
                let val tlo = trexp lo
                    val thi = trexp hi
                    val accVar = allocLocal (topLevel()) (!escape) 
                    val venv' = tabRInserta(var, Var({ty=TInt RO, access=accVar, level=getActualLev()}), venv)
                    val _ = preWhileForExp()
                    val tbody = transExp (venv', tenv) body
                    (*val expVar = varDec(accVar, #exp tlo)*)
                    val expVar = simpleVar(accVar, getActualLev())

                    val expFor = forExp {lo=(#exp tlo), hi=(#exp thi), var=expVar, body=(#exp tbody)}
                    val _ = postWhileForExp()
                in  if not (tiposIguales (#ty tlo) (TInt RW))
                    then error("Límite inferior de for no es del tipo entero", nl)
                    else if not (tiposIguales (#ty thi) (TInt RW))
                         then error("Límite superior de for no es del tipo entero", nl)
                         else {exp=expFor, ty=tipoReal((#ty tbody))}
                end
          | trexp(LetExp({decs, body}, _)) =
                let fun aux (d, (v, t, exps1)) =
                            let val (v', t', exps2 : (Trans.exp list)) = trdec (v, t) d
                            in (v', t', exps1@exps2) end
                    val (venv', tenv', expdecs) = List.foldl aux (venv, tenv, []) decs
                    val {exp=expbody, ty=tybody} = transExp (venv', tenv') body
                    val exp' = seqExp(expdecs@[expbody])
                in  {exp=exp', ty=tipoReal(tybody)}
                end
          | trexp(BreakExp nl) = 
                {exp=breakExp(), ty=TUnit} 
          | trexp(ArrayExp({typ, size, init}, nl)) =
                let val tsize = trexp size
                    val _ = if tiposIguales (#ty tsize) (TInt RW)
                            then ()
                            else error("El tamaño del arreglo no es del tipo entero", nl)
                    val (tytyp, unico) =
                        case tabBusca(typ, tenv) of
                            SOME (TArray (t, u)) => (t, u)
                          | _ => error("No está definido el array "^typ, nl)
                    val tinit = trexp init
                    val _ = if tiposIguales tytyp (#ty tinit)
                            then ()
                            else error("Valor inicial del arreglo no es del tipo indicado", nl)
                in  {exp=arrayExp{size=(#exp tsize), init=(#exp tinit)}, ty=TArray(tytyp, unico)}
                end
        and trvar(SimpleVar s, nl) = 
                let val (tvar, tacc, tlev) =
                        case tabBusca(s, venv) of
                            SOME (Var{ty, access, level}) => (ty, access, level)
                          | SOME _ => error(s^" no es una variable", nl)
                          | NONE => error(s^" no está definido", nl)
                in  {exp=simpleVar(tacc, tlev), ty=tipoReal(tvar)}
                end
          | trvar(FieldVar(v, s), nl) =
                let val (expv, fs) =
                        case trvar(v, nl) of
                            {exp, ty=TRecord(fs, u)} => (exp, fs)
                          | _ => error("No es un record", nl)
                    val (t', i') = 
                        case List.find (fn x => #1(x) = s) fs of
                            SOME (_, t', i') => (t', i')
                          | _ => error(s^" no es miembro del record", nl)
                    in {exp=fieldVar(expv, i'), ty=tipoReal(t')}
                    end
          | trvar(SubscriptVar(v, e), nl) =
                let val (exparr, tyarr) =
                        case trvar(v, nl) of
                            {exp, ty=TArray(tyarr, _)} => (exp, tyarr)
                          | _ => error((varName v)^"No es un array", nl)
                    val (expsub, tysub) =
                        case trexp e of
                            {exp, ty=TInt r} => (exp, TInt r)
                          | _ => error("Índice de array no es entero", nl)
                    val expSubsVar = subscriptVar(exparr, expsub)
                in {exp=expSubsVar, ty=tipoReal(tyarr)}
                end
        and trdec (venv, tenv) (VarDec ({name, escape, typ=NONE, init}, nl)) = 
                let val {exp=e', ty=t'} = transExp (venv, tenv) init
                    val _ = case t' of
                                 TNil => error("No se puede inicializar la variable "^name^" con Nil sin declarar su tipo", nl)
                               | _ => ()
                    val accVar = allocLocal (topLevel()) (!escape)
                    val expVar = varDec(accVar, e')
                    val nivel = getActualLev() (* #level(topLevel()) *)
                in  (tabRInserta(name, Var{ty=t', access=accVar, level=nivel}, venv), tenv, [expVar])
                end
          | trdec (venv, tenv) (VarDec ({name, escape, typ=SOME b, init}, nl)) = 
                let val {exp=e', ty=t'} = transExp (venv, tenv) init
                    val tret' = case tabBusca(b, tenv) of
                            SOME t => t
                          | NONE => error("Tipo no definido", nl)
                    val _ = if tiposIguales t' tret'
                            then ()
                            else error ("El tipo del valor inicial es incorrecto", nl)
                    val accVar = allocLocal (topLevel()) (!escape)
                    val expVar = varDec(accVar, e')
                    val nivel = getActualLev() (* #level(topLevel()) *)
                in  (tabRInserta(name, Var{ty=tret', access=accVar, level=nivel}, venv), tenv, [expVar])
                end
          | trdec (venv, tenv) (FunctionDec fs) =
                let 
                    (* transNameTy: tipa un argumento *)
                    fun transNameTy t tenv nl = case t of
                        NameTy s => (case tabBusca(s, tenv) of
                            NONE => error(s^" no está declarado", nl)
                          | SOME ty => ty)
                      | _ => error("Internal error (4)", nl)
                    fun aux0 (({name, params, result, body}, nl), (venv, tenv)) =
                        let
                            (* tipamos todos los argumentos *)
                            val typarams = List.map (fn x => transNameTy (#typ x) tenv nl) params
                            (* tipamos el retorno *)
                            val tyres = case result of
                                    NONE => TUnit
                                  | SOME t => (case tabBusca(t, tenv) of
                                            NONE => error(t^" no está declarado", nl)
                                          | SOME ty => ty)
                            (* enmascaramos el nombre de la función para evitar colisiones *)
                            val labelname = case name of
                                "_tigermain" => name
                              | _ => name^"."^makestring(nl)^"."^makestring(newLabel())

                            (* lista con los escapes de los parametros *)
                            val funext = (labelname = "_tigermain")
                            val escapparams = List.map (! o (#escape)) params
                            val escapparams' = if funext then escapparams else true::escapparams

                            (* generar nuevo level *)
                            val newlev = preFunctionDec(topLevel(), labelname, escapparams')

                            (* insertamos la función en venv *)
                            val venv' = tabRInserta(name,
                                Func {level = newlev,
                                      label = labelname,
                                      formals = typarams,
                                      result = tyres,
                                      extern = funext}, venv)
                        in
                            (* controlamos que no se repiten parametros en la función *)
                            case repite (#name) params of
                                NONE => (venv', tenv)
                              | SOME x => error(name^" repite el parámetro "^(#name x)^" en su declaración", nl)
                        end 
                    fun aux1 ( ({name, params, result, body}, nl) , (venv, tenv)) =
                        let 
                            val (funlev, funlab, funform, funres, funext) =
                                    case tabBusca(name, venv) of
                                    SOME (Func {level, label, formals, result, extern}) =>
                                            (level, label, formals, result, extern)
                                  | _ => error ("Internal error FuncionDec aux1", nl)

                            (* pushlevel *)
                            val _ = pushLevel funlev

                            (* generamos e insertamos las variables de los args en venv *)
                            fun transParam x =
                                    let val accParam = allocArg (topLevel()) (!(#escape x)) 
                                        val tyParam = transNameTy (#typ x) tenv nl
                                    in
                                        (#name x, 
                                         Var{ty=tyParam, access=accParam, level=getActualLev()})
                                    end
                            val varEntries = List.map transParam params
                            val venv' = tabInserList (venv, varEntries)

                            (* recorremos el body *)
                            val {exp=expbody, ty=tybody} = (transExp(venv', tenv) body)
                            (* funres = TUnit implica que es un procedimiento *)
                            val expfunc = functionDec(expbody, funlev, (tiposIguales funres TUnit))
                            val _ = postFunctionDec()
                            val _ = popLevel()
                        in
                            (* controlamos que el body tiene el tipo declarado del resultado *)
                            if name = "_tigermain" then (* BORRAR !!! *)
                                (venv, tenv)
                            else if tiposIguales tybody funres then
                                (venv, tenv)
                            else
                                error ("Tipo del body no coincide con el tipo del resultado.", nl) 
                        end
                    val (venv', _) = List.foldl aux0 (venv, tenv) fs
                    val (venv'', _) = List.foldl aux1 (venv', tenv) fs
                in
                    (* controlamos que no se repite declaración de la misma función en el batch *)
                    case repite (#name o #1) fs of
                        NONE => (venv'', tenv, [])
                      | SOME x => error("El batch de declaraciones repite la función " ^
                                        ((#name o #1) x), (#2 x))
                end
            (* trdec: ts es del tipo ({name: symbol, ty: ty} * pos) list *)
          | trdec (venv, tenv) (TypeDec ts) =
                let fun reps [] = false
                      | reps (({name, ...}, nl) :: t) = if List.exists (fn ({name = x, ...}, _) => x = name) t
                                                        then true
                                                        else reps t
                    val _ = if reps ts then raise Fail("nombres de tipos repetidos en el batch") else ()
                    val batch = List.map #1 ts
                    val tenv' = fijaTipos batch tenv
                                    handle Topsort.Ciclo => raise Fail("existe un ciclo en el batch")
                in  (venv, tenv', []) end
    in 
        trexp 
    end

fun transProg ex =
    let 
        val main =
            LetExp({decs=[FunctionDec[({name="_tigermain", params=[],
                        result=SOME "int", body=ex}, 0)]],
                        (*result=NONE, body=ex}, 0)]],*)
                    body=UnitExp 0}, 0)
        val _ = transExp(tab_vars, tab_tipos) main
    in  
        ()
    end

end
