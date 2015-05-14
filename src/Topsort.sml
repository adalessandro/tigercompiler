structure Topsort :> Topsort =
struct

open Tips
open Tab
open Abs
open Sres
open Tigerextras

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

fun printtenv tenv =
        map (fn x => print (("(" ^ (#1 x) ^ ", " ^ printTipo(#2 x) ^ ")") ^ "\n"))
            (tabAList tenv)

fun printvenv venv =
        map (fn x => print (("(" ^ (#1 x) ^ ", " ^ envEntry2String(#2 x) ^ ")") ^ "\n"))
            (tabAList venv)

(*  topsort genera una (symbol list) donde cada elemento depende solo de los anteriores.
 *  p es del tipo (symbol, symbol) list
 *)
fun topsort p =
            (*  candidatos filtra los elementos de st dejando solo aquellos que 
             *  no son segunda componente (el tipo dependiente) de ningún par en p *)
        let fun candidatos p st = List.filter (fn e => List.all((op<> rs e) o snd) p) st
            fun tsort p [] res = rev res
              | tsort [] st res = rev (st@res)
              | tsort p (st as (h::t)) res =
                        let val x = (hd (candidatos p st))
                                    handle Empty => raise Ciclo (* quedan elem. y no candidato *)
                        in
                            tsort (p---x) (st--x) (x::res)
                        end
            (* dada una lista de pares, genera una lista con sus elementos sin repetir *)
            fun elementos lt =
                    List.foldr
                        (fn ((x, y), l) =>
                                let val l1 = case List.find (op= rs x) l of
                                             NONE => x::l
                                           | _ => l
                                    val l2 = case List.find (op= rs y) l1 of
                                             NONE => y::l1
                                           | _ => l1
                                in l2 end) [] lt
        in tsort p (elementos p) [] end

(* buscaRecords filtra un batch dejando solo las declaraciones de Records *)
fun buscaRecords lt =
        let fun buscaRecs [] recs = recs
              | buscaRecs ((r as {name,ty=RecordTy _})::t) recs = buscaRecs t (r::recs)
              | buscaRecs (_::t) recs = buscaRecs t recs
        in
            buscaRecs lt []
        end

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

(*  procRecord inserta los records en tenv
 *  Los fields del record que tienen el tipo de un record del batch se insertan con una
 *  cabecera temporal.
 *)
fun procRecords recs env0 =
        (* buscaEnv trae el tipo de t, que debería estar en tenv salvo que sea un record *)
        let fun buscaEnv env1 t =
                    case tabBusca (t, env1) of
                    SOME (x as (TRecord _)) => TTipo (t, ref (SOME x))
                  | SOME (x as (TArray _)) => TTipo (t, ref (SOME x))
                  | SOME t' => t'
                  | NONE => case List.find (fn {name, ...} => name = t) recs of
                            SOME {name, ...} => TTipo (name, ref NONE)
                          | _ => raise Fail (t ^ " *** no existe!! error interno")
            fun precs ({name, ty=RecordTy lf}, env2) =
                    let fun aux {name, typ=NameTy t, ...} = (name, buscaEnv env2 t)
                          | aux _ = raise Fail ("Error procRecords: miembro mal definido.")
                        val lf' = List.map aux lf
                        (* enumeramos los fields *)
                        val indexes = List.tabulate (List.length lf', (fn x => x))
                        val pairs = ListPair.zip (indexes, lf')
                        val lf'' = List.map (fn (i, (x, y)) => (x, y, i)) pairs
                        val env2' = tabRInserta (name, TRecord(lf'', ref()), env2)
                    in
                        env2'
                    end
            | precs _ = raise Fail "Error interno 666"
        in
            List.foldl precs env0 recs
        end

fun fijaNone ((name, tipo), env) =
        case tipo of
        TArray (TTipo (s, ref NONE), u) => (
                case tabBusca (s, env) of
                SOME (r as (TRecord _)) => (
                    let val env' = fijaNone ((s, r), env)
                    in
                        tabRInserta (name, TArray (r, u), env')
                    end
                )
              | _ => raise Fail "Error interno 666+1"
            )
      | TRecord (lf, u) =>
                let fun trField ((s, t, n), env2) = fijaNone ((s, t), env2)
                in
                    List.foldl trField env lf
                end
      | TTipo (t, r as (ref NONE)) => (r := (SOME (tabSaca (t, env))); env)
      | TTipo (t, r as (ref (SOME x))) => (r := (SOME (tabSaca (t, env))); env)
      | _ => env

fun fijaTipos batch env =
    let (* Genera los pares de dependencias de tipo *)
        val pares = genPares batch
        (* Deja solo los records *)
        val recs = buscaRecords batch
        (* Topsort: arma una secuencia de tipos donde el i-esimo puede depender solo de
         * los anteriores *)
        val ordered = topsort pares
        (* Mete en el tenv los tipos, salvo los records *)
        val env' = procesa ordered batch recs env
        (* Mete en el tenv los records; los miembros que tienen tipo record referencian a NONE *)
        val env'' = procRecords recs env'
        (* Llegado hasta acá tenemos todos los tipos insertados,
         * donde las referencias a records del batch son TTipo(name_record, ref NONE)
         * Cambiamos las referencias a NONE, por las referencias al tipo *)
        val env''' = List.foldl fijaNone env'' (tabAList env'')
    in
        env'''
    end

end
