structure Tigergraph :> Tigergraph =
struct

type node = int 
type neighbours = {suc : node list, pred : node list}
type graph = (node, neighbours) Splaymap.dict 

fun printGraph g = let val glst = Splaymap.listItems g
                       fun ppnei {suc=suc, pred=pred} = "Suc: [" ^ String.concat (List.map (fn x => Int.toString x ^ ", ") suc) ^ "]; Pred: [" ^ String.concat (List.map (fn x => Int.toString x ^ ", ") pred) ^ "]"
                       fun pp (nod, nei) = "Nodo: " ^ Int.toString(nod) ^ "; " ^ ppnei nei ^ " \n"
                   in List.map (print o pp) glst 
                   end


fun findNode g n : neighbours = Splaymap.find (g, n)

fun nodes g = List.map (#1) (Splaymap.listItems g)

fun succ g = (#suc o (findNode g))

fun pred g = (#pred o (findNode g))

fun unionsinrep [] ys = ys
  | unionsinrep xs [] = xs
  | unionsinrep (x::xs) ys = let fun eq z = (x = z)
                                val exist = List.exists eq ys
                            in  if exist then unionsinrep xs ys else x::(unionsinrep xs ys)
                            end

fun adj g n = let val {suc=suc, pred=pred} = findNode g n
              in  unionsinrep suc pred
              end

val eq = (op =)

fun newGraph () = Splaymap.mkDict Int.compare

fun insertNode g i n = Splaymap.insert (g, i, n)

fun newNode g i = insertNode g i {suc=[], pred=[]}

exception GraphEdge

fun mk_edge g {from, to} = let val {suc=tosuc, pred=topred} = findNode g to
                               val {suc=fromsuc, pred=frompred} = findNode g from
                               val topred' = unionsinrep [from] topred
                               val fromsuc' = unionsinrep [to] fromsuc
                               val g' = insertNode g to {suc=tosuc, pred=topred'}
                               val g'' = insertNode g' from {suc=fromsuc', pred=frompred}
                           in  g''
                           end

fun rm_edge g {from, to} = let val {suc=tosuc, pred=topred} = findNode g to
                               val {suc=fromsuc, pred=frompred} = findNode g from
                               val topred' = List.filter (fn x => x <> from) topred
                               val fromsuc' = List.filter (fn x => x <> to) fromsuc
                               val g' = insertNode g to {suc=tosuc, pred=topred'}
                               val g'' = insertNode g' from {suc=fromsuc', pred=frompred}
                           in  g''
                           end

fun nodename n = Int.toString n

fun areAdj g x y = List.exists (fn z => x = z) (adj g y)

type 'a table = (node, 'a) Tigertab.Tabla

end