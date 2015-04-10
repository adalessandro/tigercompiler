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

fun getigraph (IGRAPH i) = i

fun getfgraph (FGRAPH i) = i

fun init_igraph () =
	{graph = newGraph (),
 	 tnode = (fn x => ~1),
 	 gtemp = (fn x => ""),
	 moves = []}

val gigraph = ref (IGRAPH (init_igraph()))

val gfgraph = ref (FGRAPH (init_fgraph()))

val coloredNodes = ref (Splayset.empty String.compare)
val precolored_temps = Tigerframe.specialregs @ Tigerframe.argregs
val precolored = Splayset.addList (Splayset.empty String.compare, precolored_temps)
fun isprecolored x = Splayset.member (precolored, x)

(* adjList : (Tigergraph.node, Tigergraph.node Set) Tabla *)
val adjList = ref (tabNueva())
(* degree : (Tigergraph.node, int) Tabla *)
val degree = ref (tabNueva())
(* nodetempmap : (Tigergraph.node, Tigertemp.temp) Tabla *)
val nodetempmap = ref (tabNueva())
(* moveList : (Tigergraph.node list) table :: temp_node -> instr_node Set *)
val movelist = ref (tabNueva ())
val workListMoves = ref (Splayset.empty Int.compare)

fun addEdge(u, v) =
	let val graph = ref ((#graph o getigraph) (!gigraph))
		val tnode = (#tnode o getigraph) (!gigraph)
		val gtemp = (#gtemp o getigraph) (!gigraph)
		val moves = (#moves o getigraph) (!gigraph)
    in
		(if (not (areAdj (!graph) u v) andalso u <> v)
		 then let val _ = graph := mk_edge (mk_edge (!graph) {from=u, to=v}) {from=v, to=u}
	 			  val _ = if not (isprecolored (gtemp u))
						  then (adjList := tabRInserta (u, Splayset.union ((tabSaca (u, !adjList)), (Splayset.singleton Int.compare v)), !adjList);
							    degree := tabRInserta (u, 1 + tabSaca (u, !degree), !degree))
						  else ()
				  val _ = if not (isprecolored (gtemp v))
						  then (adjList := tabRInserta (v, Splayset.union ((tabSaca (v, !adjList)), (Splayset.singleton Int.compare u)), !adjList);
							    degree := tabRInserta (v, 1 + tabSaca (v, !degree), !degree))
						  else ()
			  in ()
			  end
		 else ());
		 (gigraph := 
					(IGRAPH {graph = !graph,
							 tnode = tnode,
                             gtemp = gtemp,
                             moves = moves
                            }))
	end

fun makeIGraph (FGRAPH fgraph) (instrsblocks:(Tigerassem.instr list list)) =
    let
		val allinstr = tabClaves (#nodes fgraph)

        fun foo1 (bs, (a, p)) =
                let val newlst = List.rev (List.tabulate (List.length bs, (fn x => x + p)))
                in  (a @ [newlst], p + List.length bs)
                end
        fun foo bss = List.foldl foo1 ([], 0) bss
        val instrspos = #1 (foo instrsblocks)

        val allnodes = let val deflst = List.concat (List.map (#2) (tabAList(#def fgraph)))
                           val uselst = List.concat (List.map (#2) (tabAList(#use fgraph)))
                       in  unionsinrep deflst uselst
                       end

        val _ = List.foldl (fn (x, n) => (nodetempmap := (tabInserta (n, x, !nodetempmap)); n + 1)) 0 allnodes

        fun tnode x = #1 (tabPrimer ((fn y => x = y), !nodetempmap))
        fun gtemp x = tabSaca (x, !nodetempmap)

        val _ = List.map (fn x => adjList := tabInserta (tnode x, (Splayset.empty Int.compare), !adjList)) allnodes
        val _ = List.map (fn x => degree := tabInserta (tnode x, 0, !degree)) allnodes

        val init_inTab = List.foldr (fn (x, tab) => tabInserta (x, [], tab)) (tabNueva()) allinstr
        val init_outTab = List.foldr (fn (x, tab) => tabInserta (x, [], tab)) (tabNueva()) allinstr

		(* Liveness *)
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
        val _ = List.map (fn x => graph := (newNode (!graph) (#1 x))) (tabAList (!nodetempmap))

        val moves = ref []
        
		(* Build *)
        fun buildblock outTab blockinstrs =
                (* el liveout del bloque es el liveout de la última instrucción *)
            let val live = ref (tabSaca(hd blockinstrs, outTab))

                fun foralli n =
                    let val ismove = tabSaca(n, (#ismove fgraph))
                        val use = tabSaca(n, (#use fgraph))
                        val def = tabSaca(n, (#def fgraph))
						fun tnodepair (a, b) = (tnode a, tnode b)
                        fun foralln t = 
                                case tabBusca(tnode t, !movelist) of
                                     NONE    => movelist := tabRInserta(tnode t, (Splayset.singleton Int.compare n), !movelist)
                                   | SOME ns => movelist := tabRInserta(tnode t, (Splayset.add (ns, n)), !movelist)
                        val _ = if ismove
                                then (live := restadelist (!live) use;
                                      List.map foralln (unionsinrep def use);
                                      workListMoves := Splayset.add (!workListMoves, n);
                                      moves := unionsinrep (!moves) [tnodepair(Tigerflow.getMove n (FGRAPH fgraph))])
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

        val _ = List.map (fn x => buildblock outres x) instrspos 

		val _ = gfgraph := (FGRAPH fgraph)

		val _ = gigraph := 
					(IGRAPH {graph = (!graph),
							 tnode = tnode,
                             gtemp = gtemp,
                             moves = (!moves)
                            })

    in
        (!gigraph, outres)
    end

val spillWorkList = ref (Splayset.empty Int.compare)
val freezeWorkList = ref (Splayset.empty Int.compare)
val simplifyWorkList = ref (Splayset.empty Int.compare)
val activeMoves = ref (Splayset.empty Int.compare) (* estado inicial correcto? *)

fun makeWorkList () =
    let val tnode = (#tnode o getigraph) (!gigraph)
		val pre_initial = Splayset.addList (Splayset.empty String.compare, tabImagen (!nodetempmap))
		val initial = Splayset.difference (pre_initial, precolored)
        fun foralln n =
            if tabSaca(n, (!degree)) >= Tigerframe.genregslen then
               spillWorkList := Splayset.add (!spillWorkList, n)
            else if isMoveRelated(n) then
               freezeWorkList := Splayset.add (!freezeWorkList, n)
            else
               simplifyWorkList := Splayset.add (!simplifyWorkList, n)
    in  Splayset.app (foralln o tnode) initial
    end

and isMoveRelated n = Splayset.isEmpty (nodeMoves n)

and nodeMoves n = let val a = tabSaca(n, (!movelist))
                      val b = (!activeMoves)
                      val c = (!workListMoves)
                  in Splayset.intersection (a, (Splayset.union (b, c)))
                  end

val coalescedNodes = ref (Splayset.empty Int.compare)
val selectStack: Tigergraph.node Tigerpila.Pila = Tigerpila.nuevaPila()

fun adjacent n = let val a = tabSaca (n, (!adjList))
					 val b = Splayset.addList (Splayset.empty Int.compare, Tigerpila.toList selectStack)
					 val c = (!coalescedNodes)
				 in Splayset.difference (a, (Splayset.union (b, c)))
				 end

fun enableMoves ns = 
	let fun forallm m =
			if Splayset.member ((!activeMoves), m) then
				(activeMoves := Splayset.delete (!activeMoves, m);
				 workListMoves := Splayset.add (!workListMoves, m))
			else
				()
		fun foralln n =
			Splayset.app forallm (nodeMoves n)
	in
		Splayset.app foralln ns
	end

fun decrementDegree m =
	let val d = tabSaca(m, (!degree))
	in  (degree := tabRInserta (m, d - 1, !degree);
		 if (d = Tigerframe.genregslen) then
			(enableMoves (Splayset.add (adjacent m, m));
			 spillWorkList := Splayset.delete (!spillWorkList, m);
			 if (isMoveRelated m) then
				freezeWorkList := Splayset.add (!freezeWorkList, m)
			 else
			 	simplifyWorkList := Splayset.add (!simplifyWorkList, m))
		 else
			())
	end

val simplify =
	let fun forone n =
			(simplifyWorkList := Splayset.delete (!simplifyWorkList, n);
			 Tigerpila.pushPila selectStack n;
			 Splayset.app decrementDegree (adjacent n))
	in
		forone (getone_fromset (!simplifyWorkList))
	end

(* alias : (Tigergraph.node, Tigergraph.node) Tabla *)
val alias = ref (tabNueva())

val constrainedMoves = ref (Splayset.empty Int.compare)
val coalescedMoves = ref (Splayset.empty Int.compare)

fun getAlias n =
	if Splayset.member ((!coalescedNodes), n)
	then getAlias (tabSaca (n, (!alias)))
	else n

fun addWorkList u =
	let val gtemp = #gtemp (getigraph (!gigraph))
	in
		if (not (isprecolored (gtemp u)) andalso
			not (isMoveRelated(u)) andalso
			tabSaca(u, (!degree)) < Tigerframe.genregslen)
		then (freezeWorkList := Splayset.delete(!freezeWorkList, u);
			  simplifyWorkList := Splayset.add(!simplifyWorkList, u))
		else ()
	end

fun ok_fun (t, r) = 
	let val gtemp = #gtemp (getigraph (!gigraph))
		val graph = #graph (getigraph (!gigraph))
        val a = tabSaca(t, (!degree)) < Tigerframe.genregslen
		val b = isprecolored(gtemp t)
		val c = areAdj graph t r
	in
		a orelse b orelse c
	end

fun conservative ns =
    let fun cond n = tabSaca(n, (!degree)) >= Tigerframe.genregslen
		val foo = (fn (n, cont) => if (cond n) then cont + 1 else cont)
	in  (Splayset.foldl foo 0 ns) < Tigerframe.genregslen
	end
    
fun combine (u, v) =
	let val _ = if Splayset.member ((!freezeWorkList), v) then
					freezeWorkList := Splayset.delete(!freezeWorkList, v)
				else
					spillWorkList := Splayset.delete(!spillWorkList, v)
		val _ = (coalescedNodes := Splayset.add(!coalescedNodes, v);
				 alias := tabRInserta (v, u, (!alias)))
		val nodemoves_u = tabSaca(u, (!movelist))
		val nodemoves_v = tabSaca(v, (!movelist))
		val _ = movelist := tabRInserta(u, Splayset.union(nodemoves_u, nodemoves_v), (!movelist))
		fun forallt t =	(addEdge(t, u); decrementDegree t)
		val _ = Splayset.app forallt (adjacent v)
		val cond = (tabSaca(u, (!degree)) >= Tigerframe.genregslen) andalso
				    Splayset.member ((!freezeWorkList), u)
	in
		if cond then
			(freezeWorkList := Splayset.delete(!freezeWorkList, u);
			 spillWorkList := Splayset.add(!spillWorkList, u))
		else
			()
	end

fun coalesce () =
	let val tnode = #tnode (getigraph (!gigraph))
		val gtemp = #gtemp (getigraph (!gigraph))
		val graph = #graph (getigraph (!gigraph))
		fun tnodepair (a, b) = (tnode  a, tnode b)
		fun forone m =
			let val copy = tnodepair(Tigerflow.getMove m (!gfgraph))
				val x = getAlias(#1 copy)
				val y = getAlias(#2 copy)
				val (u, v) = if isprecolored(gtemp y)
							 then (y, x)
							 else (x, y)
				val _ = workListMoves := Splayset.delete (!workListMoves, m)
			in
				if (u = v) then
					(coalescedMoves := Splayset.add (!coalescedMoves, m);
					 addWorkList u)
				else if ((isprecolored(gtemp v)) orelse (areAdj graph u v)) then
					(constrainedMoves := Splayset.add (!constrainedMoves, m);
					 addWorkList u;
					 addWorkList v)
				else if (   (   (isprecolored(gtemp u)) andalso
						        (Splayset.find (fn t => not (ok_fun (t, u))) (adjacent(v))) = NONE
						    ) orelse
						    (   not (isprecolored(gtemp u)) andalso
							    (conservative (Splayset.union (adjacent(u), adjacent(v))))
						    )
						) then
					(coalescedMoves := Splayset.add (!coalescedMoves, m);
					 combine(u,v);
					 addWorkList u)
				else
					activeMoves := Splayset.add (!activeMoves, m)
			end
	in
		forone (getone_fromset (!workListMoves))
	end

val frozenMoves = ref (Splayset.empty Int.compare)

fun freeze () =
	let fun forone u =
		(freezeWorkList := Splayset.delete (!freezeWorkList, u);
		 simplifyWorkList := Splayset.add (!simplifyWorkList, u);
		 freezeMoves u)
	in
		forone (getone_fromset (!freezeWorkList))
	end

and freezeMoves u =
	let fun forallm m =
		let val tnode = #tnode (getigraph (!gigraph))
			fun tnodepair (a, b) = (tnode  a, tnode b)
			val copy = tnodepair(Tigerflow.getMove m (!gfgraph))
			val v = if (getAlias(#2 copy) = getAlias(u)) then
						getAlias(#1 copy)
					else
						getAlias(#2 copy)
			val _ = activeMoves := Splayset.delete (!activeMoves, m)
			val _ = frozenMoves := Splayset.add (!frozenMoves, m)
			val cond = Splayset.isEmpty(nodeMoves(v)) andalso 
					   tabSaca(v, (!degree)) < Tigerframe.genregslen
		in
			if cond then
				(freezeWorkList := Splayset.delete (!freezeWorkList, v);
				 simplifyWorkList := Splayset.add (!simplifyWorkList, v))
			else
				()
		end
	in
		Splayset.app forallm (nodeMoves u)
	end

fun selectSpill () =
	let val heuristic = getone_fromset
		fun forone m =
		(spillWorkList := Splayset.delete (!spillWorkList, m);
		 simplifyWorkList := Splayset.add (!simplifyWorkList, m);
		 freezeMoves m)
	in
		forone (heuristic (!spillWorkList))
	end

(* color : ref (Tigergraph.node, int) Tabla *)
val color = let val tnode = #tnode (getigraph (!gigraph))
				val color_tab = ref (tabNueva())
				fun precolorear (t, n) =
						(color_tab := tabRInserta (tnode t, n, (!color_tab));
						 n + 1)
			in (List.foldl precolorear 0 precolored_temps;
			    color_tab)
			end

val okColors = let val okColorsList = List.tabulate(Tigerframe.genregslen, (fn x => x))
			   in ref (Splayset.addList (Splayset.empty Int.compare, okColorsList))
			   end

val spilledNodes = ref (Splayset.empty Int.compare)

fun assignColors_while () =
	while (not (Tigerpila.isEmpty selectStack)) do
		let val gtemp = #gtemp (getigraph (!gigraph))
			val n = let val ret = Tigerpila.topPila selectStack
					in (Tigerpila.popPila selectStack; ret)
					end
			fun forallw w =
				let val cond = Splayset.member (Splayset.union (!coloredNodes, precolored), (gtemp o getAlias) w)
					val w_color = tabSaca (getAlias w, !color)
				in
					if cond then
						okColors := Splayset.delete ((!okColors), w_color)
					else 
						()
				end
		in
			Splayset.app forallw (tabSaca (n, (!adjList)));
			(if Splayset.isEmpty (!okColors) then
				spilledNodes := Splayset.add (!spilledNodes, n)
			 else
				(coloredNodes := Splayset.add (!coloredNodes, gtemp n);
				color := tabRInserta (n, getone_fromset (!okColors), (!color)))
			)
		end

fun assignColors () =
	let fun foralln n =
		let val n_color = tabSaca (getAlias n, !color)
		in color := tabRInserta (n, n_color, !color)
		end
	in 
		assignColors_while ();
		Splayset.app foralln (!coalescedNodes)
	end

end
