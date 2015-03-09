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

(* adjList : (Tigergraph.node, Tigergraph.node List) Tabla *)
val adjList = ref (tabNueva())
(* degree : (Tigergraph.node, int) Tabla *)
val degree = ref (tabNueva())
(* nodetempmap : (Tigergraph.node, Tigertemp.temp) Tabla *)
val nodetempmap = ref (tabNueva())


val precolored = Tigerframe.specialregs @ Tigerframe.argregs

fun makeIGraph (FGRAPH fgraph) (instrsblocks:(Tigerassem.instr list list)) =

    let val allinstr = tabClaves (#nodes fgraph)
        fun foo1 (bs, (a, p)) =
                let val newlst = List.rev (List.tabulate (List.length bs, (fn x => x + p)))
                in  (a @ [newlst], p + List.length bs)
                end
        fun foo bss = List.foldl foo1 ([], 0) bss
        fun tnode x = #1 (tabPrimer ((fn y => x = y), !nodetempmap))
        fun gtemp x = tabSaca (x, !nodetempmap)
        val allnodes = let val deflst = List.concat (List.map (#2) (tabAList(#def fgraph)))
                           val uselst = List.concat (List.map (#2) (tabAList(#use fgraph)))
                       in  unionsinrep deflst uselst
                       end

        val _ = List.foldr (fn (x, n) => (nodetempmap := (tabInserta (n, x, !nodetempmap)); n + 1)) 0 allnodes
        val _ = List.map (fn x => adjList := tabInserta (tnode x, [], !adjList)) allnodes
        val _ = List.map (fn x => degree := tabInserta (tnode x, 0, !degree)) allnodes

        val init_inTab = List.foldr (fn (x, tab) => tabInserta (x, [], tab)) (tabNueva()) allinstr
        val init_outTab = List.foldr (fn (x, tab) => tabInserta (x, [], tab)) (tabNueva()) allinstr

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
                val (inTab', outTab') = liveness2 inTab outTab allinstr
                
                fun eqaux (l1, l2) = Splayset.equal (list2set l1, list2set l2)
                val cond1 = tabEqRange inTab inTab' allinstr eqaux
                val cond2 = tabEqRange outTab outTab' allinstr eqaux
            in  if (cond1 andalso cond2)
                then (inTab, outTab)
                else liveness inTab' outTab'
            end
        
        val graph = ref (newGraph ())

        (* moveList : (Tigergraph.node list) table :: temp_node -> instr_node list *)
        val movelist = ref (tabNueva ())
        val workListMoves = ref (Splayset.empty Int.compare)
        
        fun buildblock outTab blockinstrs pos =
            let fun addEdge(u, v) =
                    if (areAdj (!graph) u v andalso u <> v)
                    then let val _ = graph := mk_edge (mk_edge (!graph) {from=u, to=v}) {from=v, to=u}
                             val _ = if List.exists (fn x => x = gtemp u) precolored
                                     then (adjList := tabRInserta (u, unionsinrep (tabSaca (u, !adjList)) [v], !adjList);
                                           degree := tabRInserta (u, 1 + tabSaca (u, !degree), !degree))
                                     else ()
                             val _ = if List.exists (fn x => x = gtemp v) precolored
                                     then (adjList := tabRInserta (v, unionsinrep (tabSaca (v, !adjList)) [u], !adjList);
                                           degree := tabRInserta (v, 1 + tabSaca (v, !degree), !degree))
                                     else ()
                         in ()
                         end
                    else ()

                (* el liveout del bloque es el liveout de la última instrucción *)
                val live = ref (tabSaca(hd blockinstrs, outTab))

                fun foralli n =
                    let val ismove = tabSaca(n, (#ismove fgraph))
                        val use = tabSaca(n, (#use fgraph))
                        val def = tabSaca(n, (#def fgraph))
                        fun foralln t = 
                                case tabBusca(t, !movelist) of
                                     NONE    => movelist := tabRInserta(t, [n], !movelist)
                                   | SOME ns => movelist := tabRInserta(t, unionsinrep [n] ns, !movelist)
                        val _ = if ismove
                                then (live := restadelist (!live) use;
                                      List.map foralln (unionsinrep def use);
                                      workListMoves := Splayset.add (!workListMoves, n))
                                else ()
                        val _ = live := unionsinrep (!live) def
                        
                        fun foralll x y = addEdge (tnode y, tnode x)
                        fun foralld x = List.map (foralll x) (!live)
                        val _ = List.map foralld def

                        val _ = live := unionsinrep use (restadelist (!live) def)
                    in
                        ()
                    end
            in
                List.map foralli blockinstrs
            end

        val (inres, outres) = liveness init_inTab init_outTab

        (*val _ = (print "def = [\n";
                 List.map entrypp (tabAList (#def fgraph));
                 print "]")
        val _ = (print "use = [\n";
                 List.map entrypp (tabAList (#use fgraph));
                 print "]")
        val _ = (print "inTab = [\n";
                 List.map entrypp (tabAList inres);
                 print "]")
        val _ = (print "outTab = [\n";
                 List.map entrypp (tabAList outres);
                 print "]")*)
    in
        (*#1 (build outres)*)
        (inres, outres)
    end
end
