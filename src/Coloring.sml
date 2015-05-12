structure Coloring =
struct

structure T = Tree
structure Set = Splayset

open Graph
open Tab
open Flow
open Tigerextras

fun debug x = if (!Tigerextras.enable_debug) andalso Tigerextras.coloring_debug then println x else ()

(* Variables de IGRAPH globales y funciones para manejarlas *)
datatype igraph = (* No se está usando *)
        IGRAPH of { graph: Graph.graph,
                    tnode: Temp.temp -> Graph.node,
                    gtemp: Graph.node -> Temp.temp,
                    moves: (Graph.node * Graph.node) Set.set,
                    nodes: Temp.temp Graph.table}

val gbl_graph = ref (NONE : Graph.graph option)
val gbl_tnode = ref (NONE : (Temp.temp -> Graph.node) option)
val gbl_gtemp = ref (NONE : (Graph.node -> Temp.temp) option)
val gbl_moves = ref (NONE : (Graph.node * Graph.node) Set.set option) (* No se está usando *)
val gbl_nodes = ref (NONE : Temp.temp Graph.table option) (* No se está usando *)

fun graph() = valOf (!gbl_graph)
fun tnode() = valOf (!gbl_tnode)
fun gtemp() = valOf (!gbl_gtemp)
fun moves() = valOf (!gbl_moves) (* No se está usando *)
fun nodes() = valOf (!gbl_nodes) (* No se está usando *)

fun setgraph x = gbl_graph := (SOME x)
fun settnode x = gbl_tnode := (SOME x)
fun setgtemp x = gbl_gtemp := (SOME x)
fun setmoves x = gbl_moves := (SOME x) (* No se está usando *)
fun setnodes x = gbl_nodes := (SOME x) (* No se está usando *)

(* Constantes globales *)
val precolored_temps = Frame.generalregs @ Frame.specialregs
val k_colors = Frame.generalregs
val k_len = Frame.genregslen

(* NODE WORK-LISTS, SETS AND STACKS. P.242 --------------------------------------------------------
 * Structures to keep track of graph nodes and move edges.
 * Mutually disjoint. 
 * Initially (on entry to Main), and on exiting RewriteProgram, only sets
 * precolored and initial are nonempty.
 *)

(* Machine registers, preassigned a color. *)
val precolored = ref (Set.empty Int.compare)
(* Temporary registers, not precolored and not yet processed. *)
val initial = ref (Set.empty Int.compare)
(* List of low-degree non-move-related nodes. *)
val simplifyWorkList = ref (Set.empty Int.compare)
(* Low-degree move-related nodes. *)
val freezeWorkList = ref (Set.empty Int.compare)
(* High-degree nodes. *)
val spillWorkList = ref (Set.empty Int.compare)
(* Nodes marked for spilling during this round; initially empty. *)
val spilledNodes = ref (Set.empty Int.compare)
(* Registers that have been coalesced; when u<-v is coalesced, v is added
 * to this set and u put back on some work-list (or vice versa). *)
val coalescedNodes = ref (Set.empty Int.compare)
(* Nodes successfully colored. *)
val coloredNodes = ref (Set.empty Int.compare)
(* Stack containing temporaries removed from the graph. *)
val selectStack: int Pila.Pila = Pila.nuevaPila ()


(* MOVE SETS. P.243 -------------------------------------------------------------------------------
 * Every move is in exactly one of these sets (after Build through the end of Main.
 *)

(* Moves that have been coalesced. *)
val coalescedMoves = ref (Set.empty Int.compare)
(* Moves whose source and target interfere. *)
val constrainedMoves = ref (Set.empty Int.compare)
(* Moves that will no longer be considered for coalescing. *)
val frozenMoves = ref (Set.empty Int.compare)
(* Moves enabled for possible coalescing. *)
val worklistMoves = ref (Set.empty Int.compare)
(* Moves not yet ready for coalescing. *)
val activeMoves = ref (Set.empty Int.compare)


(* OTHER DATA STRUCTURES. P.243 -------------------------------------------------------------------
 * Every move is in exactly one of these sets (after Build through the end of Main.
 *)

(* Adjacency list representation of the graph; for each non-precolored temporary u,
 * adjList[u] is the set of nodes that interfere with u. *)
val adjList = ref (tabNueva())
(* An array containing the current degree of each node. *)
val degree = ref (tabNueva())
(* A mapping from a node to the list of moves it is associated with. *)
val movelist = ref (tabNueva())
(* When a move (u, v) has been coalesced, and v put in coalescedNodes, then alias(v) = u. *)
val alias = ref (tabNueva())
(* The color chosen by the algorithm for a node; for precolored nodes this is initialized
 * to the given color *)
val color = ref (tabNueva())


(* Auxiliary functions *)
fun isprecolored x = Set.member (!precolored, x)

fun set_getone s =
        case (Set.find (fn x => true) s) of
        NONE => raise Fail "set_getone ERROR: empty set"
      | SOME x => x

fun set_forall f s = (Set.find (not o f) s = NONE)

fun set_safedelete (s, i) = (
        Set.delete (s, i)
        handle NotFound => s
  )

fun printIGraph ops =
        let fun printnodepair (a, b) = (print "("; printint a; print ", "; printint b; print ")")
            fun printIGraph' opt =            
                    case opt of
                    "graph" => Graph.printGraphNotDir (print o gtemp()) (graph())
                  | "moves" => Graph.printSet printnodepair (moves())
                  | "nodes" => Tab.printTab printint print (nodes())
                  | _ => raise Fail "printIGraph: opción desconocida"
        in
            List.map printIGraph' ops; ()
        end


(* PROGRAM CODE P.244-250 -------------------------------------------------------------------------
 * The algorithm is invoked using the procedure Main, which loops (via tail recursion)
 * until no spills are generated.
 *)

(* LivenessAnalisys and Build *)
fun makeIGraph (FGRAPH fgraph) =
        let
            val _ = debug "makeIGraph()"
            (* Initialize the interference graph *)
            val regs_set = Set.addList (Set.empty String.compare, precolored_temps) 
            val temps_set = Set.union (getTempsSet (FGRAPH fgraph), regs_set)
            val temps_list = Set.listItems temps_set
            val temps_indexes = List.tabulate (List.length temps_list, (fn x => x))
            val temps_pairs = ListPair.zip (temps_indexes, temps_list)
            val temp_nodes_tab = tabInserList (tabNueva(), temps_pairs)
            val temp_nodes_set = Set.addList (Set.empty Int.compare, temps_indexes)

            val _ = setgraph (newNodes (newGraph()) temps_indexes)
            val _ = settnode (fn t => #1 (tabPrimer ((fn y => t = y), temp_nodes_tab)))
            val _ = setgtemp (fn n => tabSaca(n, temp_nodes_tab))
            val _ = setmoves (Set.empty (pair_compare Int.compare Int.compare)) (* No se está usando *)
            val _ = setnodes temp_nodes_tab (* No se está usando *)

            (* Initialize node work-lists, sets and stacks *)
            val precolored_nodes = List.map (tnode()) precolored_temps
            val _ = precolored := Set.addList (Set.empty Int.compare, precolored_nodes)
            val _ = initial := Set.difference (temp_nodes_set, !precolored)
            val _ = simplifyWorkList := Set.empty Int.compare
            val _ = freezeWorkList := Set.empty Int.compare
            val _ = spillWorkList := Set.empty Int.compare
            val _ = spilledNodes := Set.empty Int.compare
            val _ = coalescedNodes := Set.empty Int.compare
            val _ = coloredNodes := Set.empty Int.compare
            val _ = Pila.emptyPila selectStack

            (* Initialize move sets *)
            val _ = coalescedMoves := Set.empty Int.compare
            val _ = constrainedMoves := Set.empty Int.compare
            val _ = frozenMoves := Set.empty Int.compare
            val _ = worklistMoves := Set.empty Int.compare
            val _ = activeMoves := Set.empty Int.compare

            (* Initialize the other data structures *)
            val adj_init = List.tabulate (List.length temps_list, (fn x => (x, Set.empty Int.compare)))
            val _ = adjList := tabInserList (tabNueva(), adj_init)
            val degree_init = List.tabulate (List.length temps_list, (fn x => (x, 0)))
            val _ = degree := tabInserList (tabNueva(), degree_init)
            val move_init = List.tabulate (List.length temps_list, (fn x => (x, Set.empty Int.compare)))
            val _ = movelist := tabInserList (tabNueva(), move_init)
            val alias_init = List.tabulate (List.length temps_list, (fn x => (x, x)))
            val _ = alias := tabInserList (tabNueva(), alias_init)
            val color_init = List.tabulate (List.length temps_list, (fn x => (x, "--")))
            val _ = color := tabInserList (tabNueva(), color_init)
            val _ = List.map (fn t => tabRInserta_ (tnode() t, t, color)) precolored_temps

            (* Liveness P.214 Algorithm 10.4 *)
            val instr_nodes_list = tabClaves (#nodes fgraph)
            val init_inout_pairs = List.map (fn x => (x, Set.empty String.compare)) instr_nodes_list
            val init_inout_tab = tabInserList (tabNueva(), init_inout_pairs)

            fun def n = tabSaca (n, (#def fgraph))
            fun use n = tabSaca (n, (#use fgraph))
            fun succ n = Graph.succ (#control fgraph) n
            fun ismove n = tabSaca(n, (#ismove fgraph))

            val _ = debug "liveness()"
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

            (* Build P.245 *)
            fun build i =
                let fun liveout n = tabSaca (n, outTab)
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
        in
            List.map build (List.rev instr_nodes_list)
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
        let val _ = debug "makeWorkList()"
            fun foralln n =
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

(* Simplify *)
fun simplify () =
        let val _ = debug "simplify()"
            fun forone n = (
                    simplifyWorkList := set_safedelete (!simplifyWorkList, n);
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
                spillWorkList := set_safedelete (!spillWorkList, m);
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
                        val (u, v) = if isprecolored y' then (y', x') else (x', y')
                        val _ = debug ("coalesce (u=" ^ (gtemp() u) ^ ", v=" ^ (gtemp() v) ^ ")")
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
                                (set_forall (fn t => ok_fun (t, u)) (adjacent(v)))
                            ) orelse
                            (
                                not (isprecolored u)) andalso
                                (conservative (Set.union (adjacent u, adjacent v))
                            )
                        ) then (
                            coalescedMoves := Set.add (!coalescedMoves, m);
                            combine(u, v);
                            addWorkList u
                        ) else (
                            activeMoves := Set.add (!activeMoves, m)
                        )
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
            freezeWorkList := set_safedelete (!freezeWorkList, u);
            simplifyWorkList := Set.add (!simplifyWorkList, u)
        ) else ()

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

and getAlias n =
        if Set.member (!coalescedNodes, n) then
            getAlias (tabSaca (n, (!alias)))
        else n

and combine (u, v) =
        let val _ = debug ("combine (u=" ^ (gtemp() u) ^ ", v=" ^ (gtemp() v) ^ ")")
            fun forallt t = (addEdge(t, u); decrementDegree t)
        in
            (
                if Set.member (!freezeWorkList, v) then (
                    freezeWorkList := Set.delete (!freezeWorkList, v)
                ) else (
                    spillWorkList := set_safedelete (!spillWorkList, v)
                )
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
        let val _ = debug "freeze()"
            fun forone u = (
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
                        activeMoves := set_safedelete (!activeMoves, m);
                        frozenMoves := Set.add (!frozenMoves, m);
                        if Set.isEmpty (nodeMoves v) andalso tabSaca(v, !degree) < k_len andalso
                            not (isprecolored v) then (
                            freezeWorkList := set_safedelete (!freezeWorkList, v);
                            simplifyWorkList := Set.add (!simplifyWorkList, v)
                        ) else ()
                    end
        in
            Set.app forallm (nodeMoves u)
        end

(* Select spill *)
fun selectSpill (FGRAPH fgraph) =
        let val _ = debug "selectSpill()"
            val heuristic = set_getone
            fun forone m = (
                        spillWorkList := Set.delete (!spillWorkList, m);
                        simplifyWorkList := Set.add (!simplifyWorkList, m);
                        freezeMoves (FGRAPH fgraph) m
                    )
        in
            forone (heuristic (!spillWorkList))
        end

(* AssignColors *)
fun assignColors_while () = (
    debug "assignColors_while()";
    while (not (Pila.isEmpty selectStack)) do
        let val n = Pila.popPila selectStack
            val okColorsList = k_colors
            val okColors = ref (Set.empty String.compare)
            val _ = okColors := Set.addList (!okColors, okColorsList)
            fun forallw w =
                    if Set.member (Set.union (!coloredNodes, !precolored), getAlias w) then
                        let val w_color = tabSaca (getAlias w, !color)
                        in
                            okColors := set_safedelete ((!okColors), w_color)
                        end
                    else ()
        in
            Set.app forallw (tabSaca (n, !adjList));
            if Set.isEmpty (!okColors) then (
                spilledNodes := Set.add (!spilledNodes, n)
            )
            else (
                coloredNodes := Set.add (!coloredNodes, n);
                (let val coco = set_getone (!okColors)
                in
                    tabRInserta_ (n, coco, color)
                end)
            )
        end
    )

fun assignColors () =
        let val _ = debug "assignColors()"
            fun foralln n =
                    let val n_color = tabSaca (getAlias n, !color)
                    in
                        tabRInserta_ (n, n_color, color)
                    end
        in 
            assignColors_while();
            Set.app foralln (!coalescedNodes)
        end

(* RewriteProgram *)
fun rewriteProgram (blocks : (Assem.instr list * Frame.frame) list) =
        let val _ = debug "rewriteProgram()"
            fun rewriteNode (n, (blocks' : (Assem.instr list * Frame.frame) list)) =
                    List.map (Simpleregalloc.simpleregalloc (gtemp() n)) blocks'
        in
            Set.foldl rewriteNode blocks (!spilledNodes)
        end

(* Main *)
fun coloring_main opts (blocks : (Assem.instr list * Frame.frame) list) =
        let (* For debugging *)
            val _ = debug "coloring_main()"
            val opt_flow = List.nth (opts, 0)
            val opt_interf = List.nth (opts, 1)
            val opt_color = List.nth (opts, 2)
            (* Process *)
            val instrs = (List.concat o List.map #1) blocks
            val fgraph = Flow.makeFGraph instrs
            val _ = if opt_flow then Flow.printFlow ["control", "ismove"] fgraph else ()
            val _ = makeIGraph fgraph
            val _ = if opt_interf then printIGraph ["graph"] else ()
            val _ = makeWorkList()
            fun repeat() = (
                    if not (Set.isEmpty (!simplifyWorkList)) then (simplify(); repeat())
                    else if not (Set.isEmpty (!worklistMoves)) then (coalesce fgraph; repeat())
                    else if not (Set.isEmpty (!freezeWorkList)) then (freeze fgraph; repeat())
                    else if not (Set.isEmpty (!spillWorkList)) then (selectSpill fgraph; repeat())
                    else ()
                )
            fun finish() = (
                    debug "finish called()";
                    assignColors();
                    if not (Set.isEmpty (!spilledNodes)) then
                            (coloring_main opts o rewriteProgram) blocks
                    else (
                        if opt_color then Tab.printTab (print o gtemp()) print (!color) else ();
                        debug "finish ended()";
                        blocks (* That's all folks! Just return blocks. *)
                    )
                )
        in
            repeat();
            finish()
        end

(* ReplaceTemps *)
fun replaceTemps (blocks : (Assem.instr list * Frame.frame) list) =
        let fun rep_block (is : Assem.instr list, frm : Frame.frame) =
                    let val _ = debug "replace()"
                        val color_lst = List.map (fn (a, b) => (gtemp() a, b)) (tabAList (!color))
                        (* Lista de funciones. Cada una reemplaza un temp. *)
                        val fn_lst = List.map Codegen.replace color_lst
                        (* Aplicar todos los reemplazos a una instr. *)
                        fun rep_instr i = List.foldl (fn (f, i') => f i') i fn_lst
                    in
                        List.map rep_instr is
                    end
        in
            List.map rep_block blocks
        end

fun removeMoves (instrs : Assem.instr list list) =
        let fun isredundant (Assem.MOVE {dest=dest, src=src, ...}) = (dest = src)
              | isredundant _ = false
        in
            List.map (List.filter (not o isredundant)) instrs
        end

fun coloring opts (blocks : (Assem.instr list * Frame.frame) list) =
        let val colored = coloring_main opts blocks
            fun appProcEntry (is, frm) =
                    let val {prolog, body, epilog} = Frame.procEntryExit3 (is, frm)
                    in
                        (body, frm)
                    end
            val colored' = List.map appProcEntry colored
        in
            (removeMoves o replaceTemps) colored' 
        end

end
