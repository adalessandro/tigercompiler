structure Coloring =
struct

structure T = Tree
structure Set = Splayset

open Graph
open Tab
open Flow
open Tigerextras

(*structure Graph*)
datatype igraph =
        IGRAPH of { graph: Graph.graph,
                    tnode: Temp.temp -> Graph.node,
                    gtemp: Graph.node -> Temp.temp,
                    moves: (Graph.node * Graph.node) Set.set,
                    nodes: Temp.temp Graph.table}

(* Variables de IGRAPH globales y funciones para manejarlas *)
val gbl_graph = ref (NONE : Graph.graph option)
val gbl_tnode = ref (NONE : (Temp.temp -> Graph.node) option)
val gbl_gtemp = ref (NONE : (Graph.node -> Temp.temp) option)
val gbl_moves = ref (NONE : (Graph.node * Graph.node) Set.set option)
val gbl_nodes = ref (NONE : Temp.temp Graph.table option)

fun graph() = valOf (!gbl_graph)
fun tnode() = valOf (!gbl_tnode)
fun gtemp() = valOf (!gbl_gtemp)
fun moves() = valOf (!gbl_moves)
fun nodes() = valOf (!gbl_nodes)

fun setgraph x = gbl_graph := (SOME x)
fun settnode x = gbl_tnode := (SOME x)
fun setgtemp x = gbl_gtemp := (SOME x)
fun setmoves x = gbl_moves := (SOME x)
fun setnodes x = gbl_nodes := (SOME x)

(* Constantes globales *)
val precolored_temps = Frame.specialregs @ Frame.argregs
val precolored_nodes = List.map (tnode()) precolored_temps
val k_len = Frame.genregslen

(* Estructuras globales para el coloreo *)
val movelist = ref (tabNueva())
val worklistMoves = ref (Set.empty Int.compare)
val adjList = ref (tabNueva())

val precolored = Set.addList (Set.empty Int.compare, precolored_nodes)
fun isprecolored x = Set.member (precolored, x)
val degree = ref (tabNueva())
val coloredNodes = ref (Set.empty Int.compare)

val spillWorkList = ref (Set.empty Int.compare)
val freezeWorkList = ref (Set.empty Int.compare)
val simplifyWorkList = ref (Set.empty Int.compare)
val activeMoves = ref (Set.empty Int.compare) (* estado inicial correcto? *)

val initial = ref (Set.empty Int.compare)

val coalescedNodes = ref (Set.empty Int.compare)
val selectStack: int Pila.Pila = Pila.nuevaPila ()

val alias = ref (tabNueva())
val constrainedMoves = ref (Set.empty Int.compare)
val coalescedMoves = ref (Set.empty Int.compare)

val frozenMoves = ref (Set.empty Int.compare)

val color = ref (tabNueva())
val okColors = ref (Set.empty Int.compare)
val spilledNodes = ref (Set.empty Int.compare)

(* Graph coloring implementation algorithm *)

(* LivenessAnalisys and Build *)
fun makeIGraph (FGRAPH fgraph) =
        let
            val temps_set = getTempsSet (FGRAPH fgraph)
            val temps_list = Set.listItems temps_set
            val temps_indexes = List.tabulate (List.length temps_list, (fn x => x))
            val temps_pairs = ListPair.zip (temps_indexes, temps_list)
            val temp_nodes = tabInserList(tabNueva(), temps_pairs)

            val _ = settnode (fn t => #1 (tabPrimer ((fn y => t = y), temp_nodes)))
            val _ = setgtemp (fn n => tabSaca(n, temp_nodes))

            val instr_nodes_list = tabClaves (#nodes fgraph)
            val init_inout_pairs = List.map (fn x => (x, Set.empty String.compare)) instr_nodes_list
            val init_inout_tab = tabInserList (tabNueva(), init_inout_pairs)

            fun def n = tabSaca (n, (#def fgraph))
            fun use n = tabSaca (n, (#use fgraph))
            fun succ n = Graph.succ (#control fgraph) n
            fun ismove n = tabSaca(n, (#ismove fgraph))

            (* Liveness P.214 Algorithm 10.4 *)
            fun liveness (inTab, outTab) =
                let fun liveness' (inTab', outTab', []) = (inTab', outTab')
                      | liveness' (inTab', outTab', (n::ns)) =
                            let fun liveout n = tabSaca (n, outTab')
                                fun livein n = tabSaca (n, inTab')
                                val newin = Set.union (use n, (Set.difference (liveout n, def n)))
                                fun aux (x, s) = Set.union (livein x, s)
                                val newout = Set.foldl aux (Set.empty String.compare) (succ n)
                                val inTab'' = tabRInserta (n, newin, inTab')
                                val outTab'' = tabRInserta (n, newout, outTab')
                            in
                                liveness' (inTab'', outTab'', ns)
                            end
                    val (inTab', outTab') = liveness' (inTab, outTab, instr_nodes_list)
                in
                    if tabEq Set.equal (inTab, inTab') andalso tabEq Set.equal (outTab, outTab') then
                        (inTab, outTab)
                    else
                        liveness (inTab', outTab')
                end
            
            val (inTab, outTab) = liveness (init_inout_tab, init_inout_tab)

            (* Initialization *)
            val _ = setmoves (Set.empty (pair_compare Int.compare Int.compare))
            val _ = setnodes (tabNueva())

            (* Build P.245 *)
            fun build i =
                let fun liveout n = tabSaca (n, outTab)
                    fun livein n = tabSaca (n, inTab)
                    val live = liveout i
                    fun foralln n = 
                            let val is = tabSaca (tnode() n, !movelist)
                            in
                                tabRInserta_ (tnode() n, (Set.add (is, i)), movelist)
                            end
                    val live' = if ismove i then (
                                    Set.app foralln (Set.union (def i, use i));
                                    worklistMoves := Set.add (!worklistMoves, i);
                                    Set.difference (live, (use i))
                                ) else
                                    live
                    val live'' = Set.union (live', (def i))
                    fun foralld x = 
                            let fun foralll y = addEdge (tnode() y, tnode() x)
                            in
                                Set.app foralll live''
                            end
                in
                    Set.app foralld (def i)
                end

            val init_graph = newNodes (newGraph ()) temps_indexes
        in
            List.map build instr_nodes_list
        end

and addEdge(u, v) =
        if (not (areAdj (graph()) u v) andalso u <> v) then (
            setgraph (mk_edge (mk_edge (graph()) {from=u, to=v}) {from=v, to=u});
            if not (isprecolored u) then (
                tabRInserta_ (u, Set.add (tabSaca (u, !adjList), v), adjList);
                tabRInserta_ (u, 1 + tabSaca (u, !degree), degree)
            ) else ();
            if not (isprecolored v) then (
                tabRInserta_ (v, Set.add (tabSaca (v, !adjList), u), adjList);
                tabRInserta_ (v, 1 + tabSaca (v, !degree), degree)
            ) else ()
         ) else ()

fun makeWorkList () =
        let fun foralln n =
                    if tabSaca(n, (!degree)) >= k_len then
                        spillWorkList := Set.add (!spillWorkList, n)
                    else if isMoveRelated(n) then
                        freezeWorkList := Set.add (!freezeWorkList, n)
                    else
                        simplifyWorkList := Set.add (!simplifyWorkList, n)
        in
            Set.app foralln (!initial)
        end

and adjacent n =
        let val a = tabSaca (n, (!adjList))
            val b = Set.addList (Set.empty Int.compare, Pila.toList selectStack)
            val c = (!coalescedNodes)
        in
            Set.difference (a, (Set.union (b, c)))
        end

and nodeMoves n =
        let val a = tabSaca(n, (!movelist))
            val b = (!activeMoves)
            val c = (!worklistMoves)
        in
            Set.intersection (a, (Set.union (b, c)))
        end

and isMoveRelated n = Set.isEmpty (nodeMoves n)

fun set_getone s =
        case (Set.find (fn x => true) s) of
        NONE => raise Fail "getone_fromset ERROR: empty set"
      | SOME x => x

fun set_forall f s = (Set.find f s = NONE)

(* Simplify *)
fun simplify () =
        let fun forone n = (
                    simplifyWorkList := Set.delete (!simplifyWorkList, n);
                    Pila.pushPila selectStack n;
                    Set.app decrementDegree (adjacent n)
                    )
        in
            forone (set_getone (!simplifyWorkList))
        end

and decrementDegree m =
        let val d = tabSaca(m, !degree)
        in
            tabRInserta_ (m, (d-1), degree);
            if (d = k_len) then (
                enableMoves (Set.add (adjacent m, m));
                spillWorkList := Set.delete (!spillWorkList, m);
                if (isMoveRelated m) then
                    freezeWorkList := Set.add (!freezeWorkList, m)
                else
                    simplifyWorkList := Set.add (!simplifyWorkList, m)
            ) else ()
        end

and enableMoves ns = 
        let fun forallm m =
                    if Set.member (!activeMoves, m) then (
                        activeMoves := Set.delete (!activeMoves, m);
                        worklistMoves := Set.add (!worklistMoves, m)
                    ) else ()
            fun foralln n = 
                    Set.app forallm (nodeMoves n)
        in
            Set.app foralln ns
        end

(* Coalesce *)
fun coalesce (FGRAPH fgraph) =
        let fun forone m =
                    let val m' = Flow.getMove (FGRAPH fgraph) m
                        val x = (tnode() o #1) m'
                        val y = (tnode() o #2) m'
                        val x' = getAlias x
                        val y' = getAlias y
                        val (u, v) = if isprecolored y' then (y, x) else (x, y)
                    in
                        worklistMoves := Set.delete (!worklistMoves, m);
                        if (u = v) then (
                            coalescedMoves := Set.add (!coalescedMoves, m);
                            addWorkList u
                        ) else if isprecolored v orelse areAdj (graph()) u v then (
                            constrainedMoves := Set.add (!constrainedMoves, m);
                            addWorkList u;
                            addWorkList v
                        ) else if (
                            (
                                isprecolored u andalso
                                (set_forall (fn t => not (ok_fun (t, u))) (adjacent(v)))
                            ) orelse
                            (
                                not (isprecolored u)) andalso
                                (conservative (Set.union (adjacent u, adjacent v))
                            )
                        ) then (
                            coalescedMoves := Set.add (!coalescedMoves, m);
                            combine(u, v);
                            addWorkList u
                        ) else
                            activeMoves := Set.add (!activeMoves, m)
                    end
        in
            forone (set_getone (!worklistMoves))
        end

and addWorkList u =
        if (
            not (isprecolored u) andalso
            not (isMoveRelated u) andalso
            tabSaca(u, (!degree)) < k_len
        ) then (
            freezeWorkList := Set.delete (!freezeWorkList, u);
            simplifyWorkList := Set.add (!simplifyWorkList, u)
        ) else ()

and getAlias n =
        if Set.member (!coalescedNodes, n) then
            getAlias (tabSaca (n, (!alias)))
        else n

and ok_fun (t, r) = 
        let val a = tabSaca(t, (!degree)) < k_len
            val b = isprecolored t
            val c = areAdj (graph()) t r
        in
            a orelse b orelse c
        end

and conservative ns =
        let fun cond n = tabSaca(n, (!degree)) >= k_len
            val foo = (fn (n, cont) => if cond n then cont + 1 else cont)
        in
            (Set.foldl foo 0 ns) < k_len
        end
    
and combine (u, v) =
        let fun forallt t = (addEdge(t, u); decrementDegree t)
        in
            (
                if Set.member (!freezeWorkList, v) then
                    freezeWorkList := Set.delete (!freezeWorkList, v)
                else
                    spillWorkList := Set.delete (!spillWorkList, v)
            );
            coalescedNodes := Set.add (!coalescedNodes, v);
            tabRInserta_ (v, u, alias);
            tabRInserta_ (u, Set.union (tabSaca (u, !movelist), tabSaca (v, !movelist)), movelist);
            Set.app forallt (adjacent v);
            if (tabSaca(u, !degree) >= k_len) andalso Set.member (!freezeWorkList, u) then (
                freezeWorkList := Set.delete (!freezeWorkList, u);
                spillWorkList := Set.add (!spillWorkList, u)
            ) else ()
        end

(* Freeze *)
fun freeze (FGRAPH fgraph) =
        let fun forone u = (
                        freezeWorkList := Set.delete (!freezeWorkList, u);
                        simplifyWorkList := Set.add (!simplifyWorkList, u);
                        freezeMoves (FGRAPH fgraph) u
                    )
        in
            forone (set_getone (!freezeWorkList))
        end

and freezeMoves (FGRAPH fgraph) u =
        let fun forallm m =
                    let val m' = Flow.getMove (FGRAPH fgraph) m
                        val x = (tnode() o #1) m'
                        val y = (tnode() o #2) m'
                        val v = if (getAlias y = getAlias u) then
                                    getAlias x
                                else
                                    getAlias y
                    in
                        activeMoves := Set.delete (!activeMoves, m);
                        frozenMoves := Set.add (!frozenMoves, m);
                        if Set.isEmpty (nodeMoves v) andalso tabSaca(v, !degree) < k_len then (
                            freezeWorkList := Set.delete (!freezeWorkList, v);
                            simplifyWorkList := Set.add (!simplifyWorkList, v)
                        ) else ()
                    end
        in
            Set.app forallm (nodeMoves u)
        end

(* Select spill *)
fun selectSpill (FGRAPH fgraph) =
        let val heuristic = set_getone
            fun forone m = (
                        spillWorkList := Set.delete (!spillWorkList, m);
                        simplifyWorkList := Set.add (!simplifyWorkList, m);
                        freezeMoves (FGRAPH fgraph) m
                    )
        in
            forone (heuristic (!spillWorkList))
        end

(* AssignColors *)
fun assignColors_while () =
    while (not (Pila.isEmpty selectStack)) do
        let val n = Pila.popPila selectStack
            val okColorsList = List.tabulate (k_len, (fn x => x))
            val _ = okColors := Set.addList (Set.empty Int.compare, okColorsList)
            fun forallw w =
                    let val cond = Set.member (Set.union (!coloredNodes, precolored), getAlias w)
                        val w_color = tabSaca (getAlias w, !color)
                    in
                        if cond then
                            okColors := Set.delete ((!okColors), w_color)
                        else ()
                    end
        in
            Set.app forallw (tabSaca (n, !adjList));
            if Set.isEmpty (!okColors) then
                spilledNodes := Set.add (!spilledNodes, n)
            else
                coloredNodes := Set.add (!coloredNodes, n);
                tabRInserta_ (n, set_getone (!okColors), color)
        end

fun assignColors () =
        let fun foralln n =
                    let val n_color = tabSaca (getAlias n, !color)
                    in
                        tabRInserta_ (n, n_color, color)
                    end
        in 
            assignColors_while ();
            Set.app foralln (!coalescedNodes)
        end

fun rewriteProgram bframes (instrsblocks : (Assem.instr list list)) =
        let fun rewriteNode (n, instrsblocks') =
                    let val pares = ListPair.zip (instrsblocks', bframes)
                        fun isSpillInstr i =
                                let val temps = Assem.getTemps i
                                in
                                    List.exists (fn x => x = gtemp() n) temps
                                end
                        fun rewriteInstr f i =
                                if isSpillInstr i then
                                    Simpleregalloc.simpleregalloc f [i]
                                else [i]
                        fun rewriteBlock (is, f) =
                                List.concat (List.map (rewriteInstr f) is)
                    in
                        List.map rewriteBlock pares
                    end
            val result = Set.foldr rewriteNode instrsblocks (!spilledNodes)
            val newTemps = Set.empty Int.compare (* simpleregalloc usa un registro en vez de temp *)
        in
            spilledNodes := Set.empty Int.compare;
            initial := Set.union (Set.union (!coloredNodes, !coalescedNodes), newTemps);
            coloredNodes := Set.empty Int.compare;
            coalescedNodes := Set.empty Int.compare;
            result
        end

end
