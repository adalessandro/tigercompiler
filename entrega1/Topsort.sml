structure Topsort :> Topsort =
struct

open Tigertips
open Tigertab
open Tigerabs

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

fun topsort p =
    let fun candidatos p e = List.filter (fn e => List.all((op<> rs e) o snd) p) e
        fun tsort p [] res = rev res
          | tsort [] st res = rev (st@res)
          | tsort p (st as (h::t)) res =
                let val x = (hd(candidatos p st)) handle Empty => raise Ciclo
                in tsort (p---x) (st--x) (x::res) end
        fun elementos lt =
            List.foldr ( fn((x,y), l) =>
                let val l1 = case List.find (op= rs x) l of
                                  NONE => x::l
                                | _ => l
                    val l2 = case List.find (op= rs y) l1 of
                                  NONE => y::l1
                                | _ => l1
                in l2 end) [] lt
    in tsort p (elementos p) [] end

fun buscaRecords lt =
    let fun buscaRecs [] recs = recs
          | buscaRecs ((r as {name,ty=RecordTy _})::t) recs = buscaRecs t (r::recs)
          | buscaRecs ((r as {name,ty=ArrayTy _})::t) recs = buscaRecs t (r::recs)
          | buscaRecs (_::t) recs = buscaRecs t recs
    in buscaRecs lt [] end

fun genPares lt =
    let val lrecs = buscaRecords lt
        fun genP [] res = res
          | genP ({name,ty=NameTy s}::t) res = genP t ((s,name)::res)
          | genP ({name,ty=ArrayTy s}::t) res = genP t ((s,name)::res)
          | genP ({name,ty=RecordTy lf}::t) res =
                let fun recorre({typ=NameTy x,...}::t) = (* los records permiten referencias circulares entre sí *)
                        (case List.find ((op= rs x) o #name) lrecs of
                              SOME _ => recorre t (*si es un record definido en este batch, lo salteamos*)
                            | NONE => x::recorre t) (*caso contrario devuelve el par*)
                      | recorre(_::t) = raise Fail ("error semántico, un field tiene que ser de un tipo ya definido") (*recorre t*)
                      | recorre [] = []
                    val res' = recorre lf
                    val res'' = List.map (fn x => (x, name)) res'
                in genP t (res''@res) end
       in genP lt [] end

fun procesa [] batch recs env = env
  | procesa (sorted as (h::t)) (batch : {name: symbol, ty: ty} list) (recs : {name: symbol, ty: ty} list) env =
       let fun filt h {name,ty=NameTy t} = h = t
             | filt h {name,ty=ArrayTy t} = false (*h = t*)
             | filt h {name,ty=RecordTy lt} = false (*List.exists ((h ls op=) o #name) lt*)
           val (ps,ps') = List.partition (filt h) batch
           val ttopt = case List.find ((h ls op=) o #name) recs of
                            SOME _ => NONE (* lo records se procesan después *)
                          | NONE => case tabBusca(h,env) of
                                         SOME t => SOME t
                                       | _ => raise Fail (h^" no existe")
           val env' = case ttopt of
                           SOME tt => List.foldr (fn ({name,ty=NameTy _},env') => (tabRInserta(name,tt,env))
                                                   | ({name,ty=ArrayTy _},env') => tabRInserta(name,TArray (tt, ref ()), env')
                                                   | ({name,...},_) => raise Fail ("Error interno 666+2 "^name)
                                                 ) env ps
                         | _ => env
       in procesa t ps' recs env' end

fun procRecords recs env =
    let fun buscaEnv env' t = 
            case tabBusca (t,env) of
                 SOME (x as (TRecord _)) => TTipo (t, ref (SOME x))
               | SOME (x as (TArray _)) => TTipo (t, ref (SOME x))
               | SOME t' => t'
               (*| NONE => case tabBusca(t, env') of
                              SOME (x as (TRecord _)) => TTipo (t, ref (SOME x))
                            | SOME t' => t'*)
                            | NONE => case List.find (fn {name,...} => name = t) recs of
                                           SOME {name,...} => (print(name^"NONErefHOLA\n"); TTipo (name, ref NONE))
                                         | _ => raise Fail (t^" *** no existe!!")
        fun precs [] env' = env'
          | precs ({name, ty=RecordTy lf}::t) env' =
                let val lf' = List.foldl (fn ({name, typ=NameTy t, ...}, l) => (name, buscaEnv env' t) :: l
                                           (*| ({name, typ=ArrayTy t, ...}, l) => (name, TArray(buscaEnv env' t, ref ())) :: l*)
                                           | (_, l) => raise Fail ("Error interno miembro mal definido. procRecords.") (*l*)
                                         ) [] lf
                    val (_, lf'') = List.foldl (fn ((x,y), (n,l)) => (n+1, (x,y,n)::l)) (0,[]) lf'
                    val env'' = tabRInserta (name, TRecord (lf'', ref()), env')
                in precs t env'' end
          | precs ({name, ty=ArrayTy s}::t) env' =
                let val arrty = buscaEnv env' s
                    val env'' = tabRInserta (name, TArray (arrty, ref()), env')
                in precs t env'' end
          | precs _ _ = raise Fail "Error interno 666"
    in precs recs env end

 (* Encuentra NONEs y los reemplaza con su tipo en el env *)
 (* fijaNONE lista env: los miembros de lista son pares (symbol, Tipo) *)
    fun fijaNONE [] env = env
      | fijaNONE ((name, TArray (TTipo (s, ref NONE), u)) :: t) env =
            (case tabBusca(s, env) of
                  SOME (r as (TRecord _)) => fijaNONE t (tabRInserta (name, TArray (r, u) , env))
                | SOME _ => raise Fail (s ^ " no record!")
                | _ => raise Fail (s^": Tipo inexistente"))
      | fijaNONE ((name, TRecord (lf, u)) :: t) env =
            let
                fun busNONE ((s, TTipo (t, ref NONE), i), l) =
                    (case tabBusca(t, env) of
                          SOME (tt as (TRecord _)) => (s, TTipo (t, ref (SOME tt)), i) :: l
                        | SOME _ => raise Fail (s ^ " no record!")
                        | _ => raise Fail (s^": Tipo inexistente"))
                  | busNONE (d, l) = d :: l
                val lf' = List.foldr busNONE [] lf
            in fijaNONE t (tabRInserta(name, TRecord (lf', u), env)) end
      | fijaNONE ((name, TTipo (s, ref NONE)) :: t) env =
            (case tabBusca (s, env) of
                  SOME (r as (TRecord _)) => fijaNONE t (tabRInserta (name, r, env))
                | SOME _ => raise Fail (s ^ " no record!")
                | _ => raise Fail (s^": Tipo inexistente"))
      | fijaNONE (_::t) env = fijaNONE t env

fun fijaRecords decs env =
  let fun buscaEnv t = case tabBusca (t,env) of
                            SOME t' => t'
                          | _ => raise Fail (t^" no existe!!")
      fun fija1 (name, TTipo (s, x),n) = (x := (SOME (buscaEnv s)))
        | fija1 x = ()
      fun fija (name, TRecord(lf,u)) = (List.map fija1 lf)
        | fija x = []
   in List.map fija decs end

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
        val _ = print "----------Despues de procRecords---------\n"
        val _ = printtenv env''
        val env''' = fijaNONE (tabAList env'') env'' (*cambia las referencias a NONE por las referencias al tipo*)
        val _ = print "--------Antes de fijaRecords---------------\n"
        val _ = fijaRecords (tabAList env''') env''' (*cambia las referencias a NONE de los fields de records que referencian a un record recien agregado*)
        val _ = print "--------Despues de fijaRecords---------------\n"
        val _ = printtenv env'''
    in env''' end

end
