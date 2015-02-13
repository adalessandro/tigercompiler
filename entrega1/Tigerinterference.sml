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

fun makeIGraph (FGRAPH fgraph) =
    let val allinstr = tabClaves (#nodes fgraph)
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
                            val _ = (print "["; List.map print use; print "]\n")
                            
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

        fun build outTab =
            let val init_workListMoves = Splayset.empty Int.compare
                val init_graph = newGraph ()
                (* moveList : (Tigergraph.node list) table :: temp_node -> instr_node list *)
                val init_moveList = tabNueva () 

                fun addEdge(gr, u, v) =
                    if (areAdj gr u v andalso u <> v)
                    then let val gr' = mk_edge (mk_edge gr {from=u, to=v}) {from=v, to=u}
                             val _ = if List.exists (fn x => x = gtemp u) precolored
                                     then (adjList := tabRInserta (u, unionsinrep (tabSaca (u, !adjList)) [v], !adjList);
                                           degree := tabRInserta (u, 1 + tabSaca (u, !degree), !degree))
                                     else ()
                             val _ = if List.exists (fn x => x = gtemp v) precolored
                                     then (adjList := tabRInserta (v, unionsinrep (tabSaca (v, !adjList)) [u], !adjList);
                                           degree := tabRInserta (v, 1 + tabSaca (v, !degree), !degree))
                                     else ()
                         in gr'
                         end
                    else gr

                fun buildinstr (n, (graph, moveList, workListMoves)) =
                    let val live = tabSaca(n, outTab)
                        val ismove = tabSaca(n, (#ismove fgraph))
                        val use = tabSaca(n, (#use fgraph))
                        val def = tabSaca(n, (#def fgraph))
                        val (live', moveList', workListMoves') =
                            if ismove
                            then let val live' = restadelist live use
                                     fun foralln (t, mvlst) = case tabBusca(t, mvlst) of
                                                                   NONE => tabRInserta(t, [n], mvlst)
                                                                 | SOME ns => tabRInserta(t, unionsinrep [n] ns, mvlst)
                                     val mvlst' = List.foldr foralln moveList (unionsinrep def use)
                                     val workListMoves' = Splayset.add (workListMoves, n)
                                 in
                                     (live', mvlst', workListMoves')
                                 end
                            else
                                 (live, moveList, workListMoves)
                        val live'' = unionsinrep live' def
                        fun foralld (d, gra1) =
                            let fun foralll (l, gra2) = addEdge(gra2, tnode d, tnode l)
                            in  List.foldr foralll gra1 live''
                            end
                        val graph' = List.foldr foralld graph def
                        (* val live''' = unionsinrep use (restadelist live'' def) *)
                    in
                        printGraph graph';
                        (graph', moveList', workListMoves')
                    end
            in
                List.foldr buildinstr (init_graph, init_moveList, init_workListMoves) allinstr
            end
        val (inres, outres) = liveness init_inTab init_outTab
        fun entry2pp y = print (y ^ ",")
        fun entrypp (x, ys) = (print ( "( " ^ (Int.toString x) ^ ", [");
                               List.map entry2pp ys;
                               print "] )\n")
        val _ = (print "def = [\n";
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
                 print "]")
    in
        
        #1 (build outres)
    end
end
