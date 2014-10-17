structure Tigerseman :> Tigerseman =
struct

open Tigerabs
open Tigersres
open Topsort

(* Tipo temporal *)
datatype SCAF = SCAF

(* label gen temporal *)
local
    val n = ref 0
in
    fun newLabel() = !n before n:= !n + 1
end

(* Expresión tipada *)
type expty = {exp: SCAF, ty: Tipo}

(* Tipo tabla espacio de nombres de variables y funciones *)
type venv = (string, EnvEntry) Tigertab.Tabla

(* Tipo tabla espacio de nombres de tipos *)
type tenv = (string, Tipo) Tigertab.Tabla

(* Tabla inicial del espacio de nombres de variables y funciones *)
val tab_vars : (string, EnvEntry) Tabla = tabInserList(
    tabNueva(),
    [("print", Func{level=mainLevel, label="print",
        formals=[TString], result=TUnit, extern=true}),
    ("flush", Func{level=mainLevel, label="flush",
        formals=[], result=TUnit, extern=true}),
    ("getchar", Func{level=mainLevel, label="getstr",
        formals=[], result=TString, extern=true}),
    ("ord", Func{level=mainLevel, label="ord",
        formals=[TString], result=TInt RW, extern=true}),
    ("chr", Func{level=mainLevel, label="chr",
        formals=[TInt RW], result=TString, extern=true}),
    ("size", Func{level=mainLevel, label="size",
        formals=[TString], result=TInt RW, extern=true}),
    ("substring", Func{level=mainLevel, label="substring",
        formals=[TString, TInt RW, TInt RW], result=TString, extern=true}),
    ("concat", Func{level=mainLevel, label="concat",
        formals=[TString, TString], result=TString, extern=true}),
    ("not", Func{level=mainLevel, label="not",
        formals=[TInt RW], result=TInt RW, extern=true}),
    ("exit", Func{level=mainLevel, label="exit",
        formals=[TInt RW], result=TUnit, extern=true})
    ])

(* Tabla inicial del espacio de nombres de tipos *)
val tab_tipos : (string, Tipo) Tabla = 
    tabInserList(
        tabNueva(),
        [("int", TInt RW), ("string", TString)]
    )

(* tipoReal: Tigertips.Tipo -> Tigertips.Tipo
    Devuelve el tipo original de un sinónimo de tipo *)
fun tipoReal (TTipo (s, ref (SOME (t)))) = tipoReal t
  | tipoReal t = t

(* tiposIguales: Tigertips.Tipo -> Tigertips.Tipo -> bool
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

(* transExp: venv -> tenv -> Tigerabs.exp -> 
    Tipa una expr con los entornos venv, tenv. *)
fun transExp(venv, tenv) =
    let fun error(s, p) = raise Fail ("Error -- línea "^Int.toString(p)^": "^s^"\n")
        fun trexp(VarExp v) = trvar(v)
          | trexp(UnitExp _) = {exp=SCAF, ty=TUnit}
          | trexp(NilExp _) = {exp=SCAF, ty=TNil}
          | trexp(IntExp(i, _)) = {exp=SCAF, ty=TInt RW}
          | trexp(StringExp(s, _)) = {exp=SCAF, ty=TString}
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
                in  {exp=SCAF, ty=res}
                end
          | trexp(OpExp({left, oper=EqOp, right}, nl)) =
                let val {exp=_, ty=tyl} = trexp left
                    val {exp=_, ty=tyr} = trexp right
                in  if tiposIguales tyl tyr andalso 
                        not (tyl=TNil andalso tyr=TNil) andalso 
                        tyl<>TUnit 
                    then {exp=SCAF, ty=TInt RW}
                    else error("Tipos no comparables", nl)
                end
          | trexp(OpExp({left, oper=NeqOp, right}, nl)) = 
                let val {exp=_, ty=tyl} = trexp left
                    val {exp=_, ty=tyr} = trexp right
                in  if tiposIguales tyl tyr andalso 
                        not (tyl=TNil andalso tyr=TNil) andalso 
                        tyl<>TUnit 
                    then {exp=SCAF, ty=TInt RW}
                    else error("Tipos no comparables", nl)
                end
          | trexp(OpExp({left, oper, right}, nl)) = 
                let val {exp=_, ty=tyl} = trexp left
                    val {exp=_, ty=tyr} = trexp right
                in  if tiposIguales tyl tyr
                    then case oper of
                        PlusOp => if tiposIguales tyl (TInt RW)
                                  then {exp=SCAF, ty=TInt RW}
                                  else error("Error de tipos", nl)
                      | MinusOp => if tiposIguales tyl (TInt RW)
                                   then {exp=SCAF, ty=TInt RW}
                                   else error("Error de tipos", nl)
                      | TimesOp => if tiposIguales tyl (TInt RW)
                                   then {exp=SCAF, ty=TInt RW} 
                                   else error("Error de tipos", nl)
                      | DivideOp => if tiposIguales tyl (TInt RW)
                                    then {exp=SCAF, ty=TInt RW} 
                                    else error("Error de tipos", nl)
                      | LtOp => if tiposIguales tyl (TInt RW) orelse tiposIguales tyl (TString)
                                then {exp=SCAF, ty=TInt RW} 
                                else error("Error de tipos", nl)
                      | LeOp => if tiposIguales tyl (TInt RW) orelse tiposIguales tyl (TString)
                                then {exp=SCAF, ty=TInt RW} 
                                else error("Error de tipos", nl)
                      | GtOp => if tiposIguales tyl (TInt RW) orelse tiposIguales tyl (TString)
                                then {exp=SCAF, ty=TInt RW} 
                                else error("Error de tipos", nl)
                      | GeOp => if tiposIguales tyl (TInt RW) orelse tiposIguales tyl (TString) 
                                then {exp=SCAF, ty=TInt RW} 
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
                    fun verificar [] [] = ()
                      | verificar (c::cs) [] = error("Faltan campos", nl)
                      | verificar [] (c::cs) = error("Sobran campos", nl)
                      | verificar ((s,t,_)::cs) ((sy,{exp,ty})::ds) =
                            if s<>sy then error("Error de campo", nl)
                            else if tiposIguales ty t then verificar cs ds
                                 else error("Error de tipo del campo "^s, nl)
                    val _ = verificar cs tfields
                in  {exp=SCAF, ty=tyr}
                end
          | trexp(SeqExp(s, nl)) =
                let val lexti = map trexp s
                    val exprs = map #exp lexti
                    val {exp, ty=tipo} = hd(rev lexti)
                in  {exp=SCAF, ty=tipo}
                end
          | trexp(AssignExp({var, exp}, nl)) =
                let val {exp=expvar, ty=tyvar} = trvar(var, nl)
                    val {exp=assexp, ty=tyexp} = trexp exp
                in  if tipoReal tyvar = (TInt RO)
                    then error("Variable de solo lectura no puede ser asignada", nl)
                    else if tiposIguales tyvar tyexp
                         then {exp=SCAF, ty=TUnit}
                         else error("Los tipos no coinciden en asignación.", nl)
                end
          | trexp(IfExp({test, then', else'=SOME else'}, nl)) =
                let val {exp=testexp, ty=tytest} = trexp test
                    val {exp=thenexp, ty=tythen} = trexp then'
                    val {exp=elseexp, ty=tyelse} = trexp else'
                in  if tipoReal tytest=TInt RW andalso 
                      tiposIguales tythen tyelse 
                    then {exp=SCAF, ty=tythen}
                    else error("Error de tipos en if", nl)
                end
          | trexp(IfExp({test, then', else'=NONE}, nl)) =
                let val {exp=exptest, ty=tytest} = trexp test
                    val {exp=expthen, ty=tythen} = trexp then'
                in if tipoReal tytest=TInt RW andalso 
                      tythen=TUnit
                   then {exp=SCAF, ty=TUnit}
                   else error("Error de tipos en if", nl)
                end
          | trexp(WhileExp({test, body}, nl)) =
                let val ttest = trexp test
                    val tbody = trexp body
                    val _ = if tipoReal(#ty ttest) = TInt RW
                            then ()
                            else error("Error de tipo en la condición", nl)
                    val _ = if #ty tbody = TUnit
                            then ()
                            else error("Cuerpo de while no puede devolver un valor", nl)
                in  {exp=SCAF, ty=TUnit}
                end
          | trexp(ForExp({var, escape, lo, hi, body}, nl)) =
                let val tlo = trexp lo
                    val thi = trexp hi
                    val venv' = (tabRInserta(var, Var({ty=TInt RO}), venv))
                    val tbody = transExp (venv', tenv) body
                in  if not (tiposIguales (#ty tlo) (TInt RW))
                    then error("Límite inferior de for no es del tipo entero", nl)
                    else if not (tiposIguales (#ty thi) (TInt RW))
                         then error("Límite superior de for no es del tipo entero", nl)
                         else {exp=SCAF, ty=(#ty tbody)}
                end
          | trexp(LetExp({decs, body}, _)) =
                let val (venv', tenv', _) = 
                        List.foldl (fn (d, (v, t, _)) => trdec (v, t) d)
                            (venv, tenv, []) decs
                    val {exp=expbody, ty=tybody} = transExp (venv', tenv') body
                in  {exp=SCAF, ty=tybody}
                end
          | trexp(BreakExp nl) =
                {exp=SCAF, ty=TUnit} 
          | trexp(ArrayExp({typ, size, init}, nl)) =
                let val tsize = trexp size
                    val _ = if tiposIguales (#ty tsize) (TInt RW)
                            then ()
                            else error("El tamaño del arreglo no es del tipo entero", nl)
                    val tyarr =
                        case tabBusca(typ, tenv) of
                            SOME t => t
                          | NONE => error("Tipo no definido", nl)
                    val tinit = trexp init
                    val _ = if tiposIguales tyarr (#ty tinit)
                            then ()
                            else error("Valor inicial del arreglo no es del tipo indicado", nl)
                in  {exp=SCAF, ty=tyarr}
                end
        and trvar(SimpleVar s, nl) =
                let val tvar =
                        case tabBusca(s, venv) of
                            SOME (Var{ty}) => ty
                          | SOME _ => error(s^" no es una variable", nl)
                          | NONE => error(s^" no está definido", nl)
                in  {exp=SCAF, ty=tvar}
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
                    in {exp=SCAF, ty=t'}
                    end
          | trvar(SubscriptVar(v, e), nl) =
                let val (exparr, tyarr) =
                        case trvar(v, nl) of
                            {exp, ty=TArray(tyarr, _)} => (exp, tyarr)
                          | _ => error("No es un array", nl)
                    val (expsub, tysub) =
                        case trexp e of
                            {exp, ty=TInt RW} => (exp, TInt RW)
                          | _ => error("Índice de array no es entero", nl)
                in {exp=SCAF, ty=tyarr}
                end
        and trdec (venv, tenv) (VarDec ({name, escape, typ=NONE, init}, nl)) =
                let val {exp=e', ty=t'} = trexp(init)
                in  (tabRInserta(name, Var{ty=t'}, venv), tenv, [{exp=SCAF, ty=t'}])
                end
          | trdec (venv, tenv) (VarDec ({name, escape, typ=SOME b, init}, nl)) =
                let val {exp=e', ty=t'} = trexp(init)
                    val tret' = case tabBusca(b, tenv) of
                            SOME t => t
                          | NONE => error("Tipo no definido", nl)
                    val _ = tiposIguales t' tret'
                in  (tabRInserta(name, Var{ty=tret'}, venv), tenv, [{exp=SCAF, ty=tret'}])
                end
          | trdec (venv, tenv) (FunctionDec fs) =
                let 
                    (* transNameTy: tipa un argumento *)
                    fun transNameTy t tenv nl = case t of
                        NameTy s => (case tabBusca(s, tenv) of
                            NONE => error(s^" no está declarado", nl)
                          | SOME ty => ty)
                      | _ => error("Internal error (4)", nl)
                    (* repite key ls: devuelve SOME x si existen 2 elementos en ls que tienen el mismo key() *)
                    fun repite key = #1 o foldr (fn (x, (b, xs)) => case b of
                            SOME _ => (b, [])
                          | NONE => if (List.all (fn y => (key x) <> (key y)) xs)
                                    then (NONE, (x::xs)) else (SOME x, [])) (NONE, [])
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
                            (* insertamos la función en tenv *)
                            val venv' = tabRInserta(name,
                                Func {level = mainLevel,
                                      label = labelname,
                                      formals = typarams,
                                      result = tyres,
                                      extern = false}, venv)
                        in
                            (* controlamos que no se repiten parametros en la función *)
                            case repite (#name) params of
                                NONE => (venv', tenv)
                              | SOME x => error(name^" repite el parámetro "^(#name x)^" en su declaración", nl)
                        end 
                    fun aux1 (({name, params, result, body}, nl), (venv, tenv)) =
                        let 
                            val tyres = case tabBusca(name, venv) of
                                SOME (Func {result, ...}) => result
                              | _ => error("Internal error (5)", nl)
                            (* generamos e insertamos las variables de los args en venv *)
                            val varEntries = List.map (fn x => (#name x, Var {ty = transNameTy (#typ x) tenv nl})) params
                            val venv' = tabInserList (venv, varEntries)
                            (* tipamos el body de la función *)
                            val tybody = #ty (transExp(venv', tenv) body)
                        in
                            (* controlamos que el body tiene el tipo declarado del resultado *)
                            if tiposIguales tybody tyres 
                            then (venv, tenv)
                            else error("Tipo del body no coincide con el tipo del resultado.", nl) 
                        end
                    val (venv', _) = List.foldl aux0 (venv, tenv) fs
                    val (venv'', _) = List.foldl aux1 (venv', tenv) fs
                in
                    (* controlamos que no se repite declaración de la misma función en el batch *)
                    case repite (#name o #1) fs of
                        NONE => (venv'', tenv, [])
                      | SOME x => error("El batch de declaraciones repite la función "^((#name o #1) x), (#2 x))
                end
          | trdec (venv,tenv) (TypeDec ts) =
                let val batch = List.map #1 ts
                    val tenv' = fijaTipos batch tenv
                in  (venv, tenv', []) end
    in 
        trexp 
    end

fun transProg ex =
    let 
        val main =
            LetExp({decs=[FunctionDec[({name="_tigermain", params=[],
                        result=NONE, body=ex}, 0)]],
                    body=UnitExp 0}, 0)
        val _ = transExp(tab_vars, tab_tipos) main
    in  
        print "bien!\n" 
    end

end
