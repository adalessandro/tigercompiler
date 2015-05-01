structure Flow =
struct

structure Set = Splayset

open Graph
open Tab

(*structure Graph*)
datatype flowgraph =
        FGRAPH of { control: Graph.graph,
                    def: Temp.temp Set.set Graph.table,
                    use: Temp.temp Set.set Graph.table,
                    ismove: bool Graph.table,
                    nodes: Assem.instr Graph.table}

fun makeFGraph (instrs : Assem.instr list) =
        let val instr_indexes = List.tabulate (List.length instrs, (fn x => x))
            val instr_pairs = ListPair.zip (instr_indexes, instrs)

            fun islast pos = (List.length instrs = pos + 1)

            fun genEdge ((pos, (Assem.OPER {jump=jump, ...})), cgraph) = (
                    case jump of
                    NONE => if islast pos then
                                cgraph
                            else
                                mk_edge cgraph {from=pos, to=pos+1}
                  | SOME [l] => 
                            if l = Assem.RET_LABEL then
                                cgraph
                            else 
                                let val labpos = Assem.labelpos l instrs
                                in
                                    mk_edge cgraph {from=pos, to=labpos}
                                end
                  | SOME [l1, l2] =>
                            if l2 = Assem.FALSE_LABEL then
                                let val labpos = Assem.labelpos l1 instrs
                                    val cgnext = mk_edge cgraph {from=pos, to=pos+1}
                                in
                                    mk_edge cgnext {from=pos, to=labpos}
                                end
                            else if l2 = Assem.CALL_LABEL then
                                mk_edge cgraph {from=pos, to=pos+1}
                            else raise Fail "makeFGraph: jump malformado (1)"
                  | _ => raise Fail "makeFGraph: jump malformado (2)"
                    )
              | genEdge ((pos, (Assem.LABEL _)), cgraph)  =
                        if islast pos then
                            cgraph
                        else
                            mk_edge cgraph {from=pos, to=pos+1}
              | genEdge ((pos, (Assem.MOVE _)), cgraph) =
                    if islast pos then
                        cgraph
                    else
                        mk_edge cgraph {from=pos, to=pos+1}

            fun genMoves ((pos, i), moveTab) =
                    let val boolMove =
                                case i of 
                                Assem.MOVE _ => true
                              | _ => false
                    in
                        tabInserta (pos, boolMove, moveTab)
                    end

            fun genDefUse ((pos, i), (defT, useT)) =
                    let val (dest, src) =
                                case i of
                                Assem.OPER {dest=dest, src=src, ...} => (dest, src)
                              | Assem.LABEL _ => ([], [])
                              | Assem.MOVE {dest=dest, src=src, ...} => (dest, src)
                        fun createSet l = Set.addList ((Set.empty String.compare), l)
                        val defT' = tabInserta(pos, createSet dest, defT)
                        val useT' = tabInserta(pos, createSet src, useT)
                    in
                        (defT', useT')
                    end

            val control = newNodes (newGraph ()) instr_indexes
            val control' = List.foldl genEdge control instr_pairs

            val (def, use) = List.foldl genDefUse (tabNueva (), tabNueva ()) instr_pairs

            val ismove = List.foldl genMoves (tabNueva ()) instr_pairs

            val nodes = tabInserList(tabNueva (), instr_pairs)

        in  FGRAPH {
                control = control',
                def = def,
                use = use,
                ismove = ismove,
                nodes = nodes
            }
        end

fun getMove (FGRAPH fgraph) n =
        let val i = tabSaca (n, (#nodes fgraph))
        in
            case i of
            Assem.MOVE m => ((hd o #dest) m, (hd o #src) m)
          | _ => raise Fail "getMove: imposible!"
        end

fun getTempsSet (FGRAPH fgraph) =
        let val deflst = tabImagen (#def fgraph)
            val uselst = tabImagen (#use fgraph)
            val defset = List.foldl Set.union (Set.empty String.compare) deflst
            val useset = List.foldl Set.union (Set.empty String.compare) uselst
        in
            Set.union (defset, useset)
        end

fun printFlow [] (FGRAPH fgraph) = ()
  | printFlow (opt::ops) (FGRAPH fgraph) =
        let val intpp = print o Int.toString
            val _ =
                    case opt of
                    "control" => Graph.printGraph (print o Int.toString) (#control fgraph)
                  | "def" => Tab.printTab intpp (Graph.printSet print) (#def fgraph)
                  | "use" => Tab.printTab intpp (Graph.printSet print) (#def fgraph)
                  | "ismove" => Tab.printTab intpp (print o Bool.toString) (#ismove fgraph)
                  | "nodes" => Tab.printTab intpp (print o Assem.format) (#nodes fgraph)
                  | _ => raise Fail "printFlow: opción desconocida"
        in
            printFlow ops (FGRAPH fgraph)
        end

end
