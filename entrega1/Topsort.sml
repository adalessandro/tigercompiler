structure Topsort :> Topsort =
struct

open Tigertips
open Tigertab
open Tigerabs
open Tigersres

infix -- ---
infix rs ls

fun x ls f = fn y => f(x,y)
fun f rs y = fn x => f(x,y)
fun fst(x,_)= x and snd(_,y)= y
(* i -- e: saca las ocurrencias de e en i *)
fun i -- e = List.filter (op <> rs e) i
(* lp --- e: saca los pares en lp que comienzan con e *)
fun lp --- e = List.filter ((op <> rs e) o fst) lp

exception Ciclo

fun printtenv tenv = map (fn x => print (("("^(#1 x)^", "^printTipo(#2 x)^")")^"\n")) (tabAList tenv)

fun printvenv venv = map (fn x => print (("("^(#1 x)^", "^envEntry2String(#2 x)^")")^"\n")) (tabAList venv)

(* topsort genera una (symbol list) donde cada elemento depende solo de los anteriores.
        p es del tipo (symbol, symbol) list
 *)
fun topsort p =
            (* candidatos filtra los elementos de st dejando solo aquellos que 
                    no son segunda componente (el tipo dependiente) de ningún par en p *)
    let fun candidatos p st = List.filter (fn e => List.all((op<> rs e) o snd) p) st
        fun tsort p [] res = rev res
          | tsort [] st res = rev (st@res)
          | tsort p (st as (h::t)) res =
                let val x = (hd (candidatos p st)) handle Empty => raise Ciclo (* quedan elementos y no hay candidato, implica Ciclo *)
                in tsort (p---x) (st--x) (x::res) end
        fun elementos lt = (* dada una lista de pares, genera una lista con sus elementos sin repetir *)
            List.foldr ( fn((x,y), l) =>
                let val l1 = case List.find (op= rs x) l of
                                  NONE => x::l
                                | _ => l
                    val l2 = case List.find (op= rs y) l1 of
                                  NONE => y::l1
                                | _ => l1
                in l2 end) [] lt
    in tsort p (elementos p) [] end

(* buscaRecords filtra un batch dejando solo las declaraciones de Records y Arrays *)
fun buscaRecords lt =
    let fun buscaRecs [] recs = recs
          | buscaRecs ((r as {name,ty=RecordTy _})::t) recs = buscaRecs t (r::recs)
          | buscaRecs (_::t) recs = buscaRecs t recs
    in buscaRecs lt [] end

(* genPares toma un batch y genera los pares (p, s) que indica que el tipo s depende de p. 
        lt: es un batch de declaraciones de tipo ({name: symbol, ty: ty} list)
        NOTA: están todos los pares excepto los (r1, r2) donde r1 y r2 son records de este batch y r1 es field de r2.
 *)
fun genPares lt =
    let val lrecs = buscaRecords lt
        fun genP [] res = res
          | genP ({name, ty=NameTy s}::t) res = genP t ((s,name)::res)
          | genP ({name, ty=ArrayTy s}::t) res = genP t ((s,name)::res)
          | genP ({name, ty=RecordTy lf}::t) res =
                let fun recorre({typ=NameTy x, ...}::t) = (* los records permiten referencias circulares entre sí *)
                        (case List.find ((op= rs x) o #name) lrecs of
                              SOME _ => recorre t (* si el field es del tipo de un record definido en este batch, lo salteamos*)
                            | NONE => x::recorre t) (* caso contrario devuelve el par *)
                      | recorre(_::t) = raise Fail ("error interno genP: los fields son NameTy")
                      | recorre [] = []
                    val res' = recorre lf
                    val res'' = List.map (fn x => (x, name)) res'
                in genP t (res''@res) end
    in genP lt [] end

(* procesa sorted batch recs env: toma el primer elemento de sorted e inserta los tipos que dependen del mismo (excepto los records)
        sorted: (symbol list) devuelta por topsort
        batch:  ({name: symbol, ty: ty} list)
        recs: batch filtrado por buscaRecords
        env: el tenv (environment de tipos)
 *)
fun procesa [] batch recs env = env
  | procesa (sorted as (h::t)) (batch : {name: symbol, ty: ty} list) (recs : {name: symbol, ty: ty} list) env = (* h depende de tipos ya insertados en env *)
       let fun filt h {name, ty=NameTy t} = h = t (* filt determina si un tipo depende solo de h *)
             | filt h {name, ty=ArrayTy t} = h = t
             | filt h {name, ty=RecordTy lt} = false 
           val (ps, ps') = List.partition (filt h) batch (* ps=tipos que dependen solo de h, ps'=otros *)
           val ttopt = case List.find ((h ls op=) o #name) recs of (* ponemos en ttopt el tipo de h *)
                            SOME _ => SOME (TTipo (h, ref NONE)) (* si h es un record del batch, generamos una cabecera temporal y lo procesamos después *)
                          | NONE => case tabBusca(h, env) of (* caso contrario debería haber sido insertado en tenv *)
                                         SOME t => SOME t
                                       | _ => raise Fail (h^" no existe")
           val env' = case ttopt of
                           SOME tt => List.foldr (fn ({name,ty=NameTy _},env') => (tabRInserta(name,tt,env))
                                                   | ({name,ty=ArrayTy _},env') => tabRInserta(name,TArray (tt, ref ()), env')
                                                   | ({name,...},_) => raise Fail ("Error interno 666+2 "^name)
                                                 ) env ps
                         | _ => raise Fail ("error interno: procesa")
       in procesa t ps' recs env' end

(* procRecord inserta los records en tenv
        los fields del record que tienen el tipo de un record del batch se insertan con una cabecera temporal
 *)
fun procRecords recs env =
    let fun buscaEnv env' t = (* buscaEnv trae el tipo de t, que debería estar en tenv salvo que sea un record *)
            case tabBusca (t,env) of
                 SOME (x as (TRecord _)) => TTipo (t, ref (SOME x))
               | SOME (x as (TArray _)) => TTipo (t, ref (SOME x))
               | SOME t' => t'
               | NONE => case List.find (fn {name, ...} => name = t) recs of
                              SOME {name, ...} => TTipo(name, ref NONE)
                            | _ => raise Fail (t^" *** no existe!! error interno")
        fun precs [] env' = env'
          | precs ({name, ty=RecordTy lf}::t) env' =
                let val lf' = List.foldl (fn ({name, typ=NameTy t, ...}, l) => (name, buscaEnv env' t) :: l
                                           | (_, l) => raise Fail ("Error interno miembro mal definido. procRecords.")
                                         ) [] lf
                    val (_, lf'') = List.foldl (fn ((x,y), (n,l)) => (n+1, (x,y,n)::l)) (0,[]) lf' (* enumeramos los fields *)
                    val env'' = tabRInserta (name, TRecord (lf'', ref()), env')
                in precs t env'' end
          | precs _ _ = raise Fail "Error interno 666"
    in precs recs env end

fun fijaNone [] env = env
  | fijaNone ((name, TArray (TTipo (s, ref NONE), u))::t) env =
                     (case tabBusca (s,env) of
                           SOME (r as (TRecord _)) => fijaNone t (tabRInserta (name, TArray (r,u), env))
                         | _ => raise Fail "Error interno 666+1")
 | fijaNone ((name,TRecord (lf,u))::t) env =
       let fun busNone (s,TTipo (t, r as (ref NONE)), n) = r := (SOME (tabSaca (t,env)))
             | busNone d = ()
           val _ = List.app busNone lf
       in fijaNone t env end
 | fijaNone (_::t) env = fijaNone t env

fun fijaTipos batch env =
    let val pares = genPares batch (*genera los pares de dependencias de tipo*)
        val recs = buscaRecords batch (*deja solo los records*)
        val ordered = topsort pares (*topsort: arma una secuencia de tipos donde el i-esimo puede depender solo de los anteriores*)
        val _ = print "----------Antes de procesa---------\n"
        val env' = procesa ordered batch recs env (*mete en el tenv los tipos, salvo los records*)
        val _ = print "----------Despues de procesa---------\n"
        val _ = printtenv env'
        val _ = print "----------Antes de procRecords---------\n"
        val env'' = procRecords recs env' (*mete en el tenv los records; los miembros que tienen tipo record referencian a NONE*)
        (* llegado hasta acá tenemos todos los tipos insertados, donde las referencias a records del batch son TTipo(name_record, ref NONE) *)
        val _ = print "----------Despues de procRecords---------\n"
        val _ = printtenv env''
        val _ = print "----------Antes de fijaNone---------\n"
        val env''' = fijaNone (tabAList env'') env'' (*cambia las referencias a NONE por las referencias al tipo*)
        val _ = print "----------Despues de fijaNone---------\n"
        val _ = printtenv env'''
    in env''' end

end
