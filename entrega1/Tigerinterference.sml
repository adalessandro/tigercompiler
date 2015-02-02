structure Tigerinterference =
struct

open Tigergraph
open Tigertab
open Tigerflow
open Tigerextras

(*structure Graph*)
datatype igraph =
    IGRAPH of {graph : Tigergraph.graph,
               tnode : Tigertemp.temp -> Tigergraph.node,
               gtemp : Tigergraph.node -> Tigertemp.temp,
               moves : (Tigergraph.node * Tigergraph.node) list}

fun makeIGraph (FGRAPH fgraph) =
    let val allnodes = tabClaves (#nodes fgraph)
        fun liveness inTab outTab =
            let fun liveness2 inTab2 outTab2 [] = (inTab2, outTab2)
                  | liveness2 inTab2 outTab2 (n::ns) =
                        let val use = tabSaca (n, (#use fgraph))
                            val def = tabSaca (n, (#def fgraph))
                            val out = tabSaca (n, outTab2)
                            val newin = unionsinrep use (restadelist out def)
                            
                            val suclst = succ (#control fgraph) n
                            val inlst = List.map (fn x => tabSaca (x, inTab2)) suclst
                            val newout = List.foldr (fn (a, b) => unionsinrep a b) [] inlst

                            val inTab2' = tabRInserta (n, newin, inTab2)
                            val outTab2' = tabRInserta (n, newout, outTab2)
                        in  liveness2 inTab2' outTab2' ns
                        end
                val (inTab', outTab') = liveness2 inTab outTab allnodes
                
                fun eqaux (l1, l2) = Splayset.equal (list2set l1, list2set l2)
                val cond1 = tabEqRange inTab inTab' allnodes eqaux
                val cond2 = tabEqRange outTab outTab' allnodes eqaux
            in  if (cond1 andalso cond2)
                then (inTab, outTab)
                else liveness inTab' outTab'
            end
    in
        ()
    end

end
