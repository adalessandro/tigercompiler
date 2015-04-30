structure Graph :> Graph =
struct

structure Set = Splayset
open Tigerextras

type node = int 
type neighbours = {suc : node Set.set, pred : node Set.set}
type graph = (node, neighbours) Splaymap.dict 

fun printGraph g nodepp =
        let val glst = Splaymap.listItems g
            fun ppnei {suc=suc, pred=pred} = (
                    print "Suc: {";
                    Set.app (fn x => (nodepp x; print ", ")) suc;
                    print "}; Pred: {";
                    Set.app (fn x => (nodepp x; print ", ")) pred;
                    print "}"
                )
            fun pp (nod, nei) = (
                    print "Nodo: ";
                    nodepp nod;
                    print "; ";
                    ppnei nei;
                    print "\n"
                )
        in
            List.map pp glst 
        end

fun findNode g n : neighbours = Splaymap.find (g, n)

fun nodes g =
        let val nodes_list = List.map (#1) (Splaymap.listItems g)
        in
            Set.addList ((Set.empty Int.compare), nodes_list)
        end

fun succ g = (#suc o (findNode g))

fun pred g = (#pred o (findNode g))

fun adj g n = let val {suc=suc, pred=pred} = findNode g n
              in Set.union(suc, pred)
              end

val eq = (op =)

fun newGraph () = Splaymap.mkDict Int.compare

fun insertNode g i n = Splaymap.insert (g, i, n)

fun newNode g i = insertNode g i {suc=Set.empty Int.compare, pred=Set.empty Int.compare}

fun newNodes g [] = g
  | newNodes g (i::is) =
        let val g' = newNodes g is
        in
            newNode g' i
        end

exception GraphEdge

fun mk_edge g {from, to} = let val {suc=tosuc, pred=topred} = findNode g to
                               val {suc=fromsuc, pred=frompred} = findNode g from
                               val topred' = Set.add (topred, from)
                               val fromsuc' = Set.add (fromsuc, to)
                               val g' = insertNode g to {suc=tosuc, pred=topred'}
                               val g'' = insertNode g' from {suc=fromsuc', pred=frompred}
                           in  g''
                           end

fun rm_edge g {from, to} = let val {suc=tosuc, pred=topred} = findNode g to
                               val {suc=fromsuc, pred=frompred} = findNode g from
                               val topred' = Set.delete (topred, from)
                               val fromsuc' = Set.delete (fromsuc, to)
                               val g' = insertNode g to {suc=tosuc, pred=topred'}
                               val g'' = insertNode g' from {suc=fromsuc', pred=frompred}
                           in  g''
                           end

fun nodename n = Int.toString n

fun areAdj g x y = Set.member (adj g y, x)

type 'a table = (node, 'a) Tab.Tabla

fun entry2pp y = 
    print (y ^ ",")

fun entrypp (x, ys) = (
    print ( "( " ^ (Int.toString x) ^ ", [");
    List.map entry2pp ys;
    print "] )\n"
    )

fun entryppbool (x, b) = (
    print ( "( " ^ (Int.toString x) ^ ", ");
    if b then print "true" else print "false";
    print ")\n"
    )

end
