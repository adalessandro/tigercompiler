structure Tigerflow =
struct

open Tigergraph

(*structure Graph*)
datatype flowgraph =
    FGRAPH of {control : Tigergraph.graph,
               def : Tigertemp.temp list Tigergraph.table,
               use : Tigertemp.temp list Tigergraph.table,
               ismove: bool Tigergraph.table}

(*
        val t = Tigertab.tabNueva ()
        val t' = List.foldr (fn ((tab, n), ins) => (tabInserta (n, ins, tab), n+1)) (t, 0) instrs
*)
fun makeFGraph instrs =
    let val control = List.foldr (fn ((gra, n), _) => (newNode gra n,  n+1)) (newGraph(), 0) instrs
        val def = Tigertab.tabNueva ()
        val use = Tigertab.tabNueva ()
        val isMove = Tigertab.tabNueva ()
        fun genEdges fgraph [] = fgraph
          | genEdges fgraph (i::is) = 
                case i of
                     OPER {assem=assem, dest=dest, src=src, jump=jump} => CASE jump of

    
end
