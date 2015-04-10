structure Tigerflow =
struct

open Tigergraph
open Tigertab

(*structure Graph*)
datatype flowgraph =
    FGRAPH of {control : Tigergraph.graph,
               def : Tigertemp.temp list Tigergraph.table,
               use : Tigertemp.temp list Tigergraph.table,
               ismove: bool Tigergraph.table,
               nodes: Tigerassem.instr Tigergraph.table}

fun init_fgraph () = 
    {control = newGraph (),
    def = tabNueva(),
    use = tabNueva(),
    ismove = tabNueva(),
    nodes = tabNueva()}

fun makeFGraph (instrsblocks:(Tigerassem.instr list list)) =
    let val instrs = (List.concat o List.map List.rev) instrsblocks
        val nodes = #1 (List.foldr (fn (i, (t, n)) => (tabInserta (n, i, t),  n+1)) (tabNueva(), 0) instrs)
        val control = #1 (List.foldr (fn (_, (gra, n)) => (newNode gra n,  n+1)) (newGraph(), 0) instrs)
        val def = tabNueva ()
        val use = tabNueva ()
        val isMove = tabNueva ()
        
        fun genEdges cgraph [] _ = cgraph
          | genEdges cgraph (i::is) pos = 
                let val cgraph' = 
                    case i of
                         Tigerassem.OPER {assem=assem, dest=dest, src=src, jump=jump} =>
                             (case jump of
                                   NONE => (case is of
                                                 [] => cgraph
                                               | x::xs => mk_edge cgraph {from=pos, to=pos+1})
                                 | SOME [l] => if l = Tigerassem.RET_LABEL
                                               then cgraph
                                               else let val labpos = Tigerassem.labelpos l instrs 0
                                                    in (case labpos of
                                                             NONE => raise Fail "makeFGraph: label no encontrada"
                                                           | SOME p => mk_edge cgraph {from=pos, to=p})
                                                    end
                                 | SOME [l1, l2] => 
                                                    if l2 = Tigerassem.FALSE_LABEL then
                                                        let val labpos = Tigerassem.labelpos l1 instrs 0
                                                            val cgnext = mk_edge cgraph {from=pos, to=pos+1}
                                                        in (case labpos of
                                                                 NONE => raise Fail "makeFGraph: label no encontrada"
                                                               | SOME p => mk_edge cgnext {from=pos, to=p})
                                                        end
                                                    else if l2 = Tigerassem.CALL_LABEL then
                                                        mk_edge cgraph {from=pos, to=pos+1}
                                                    else raise Fail "makeFGraph: jump malformado (1)"
                                 | _ => raise Fail "makeFGraph: jump malformado (2)")
                       | Tigerassem.LABEL {assem=assem, lab=lab} =>
                             (case is of
                                   [] => cgraph
                                 | x::xs => mk_edge cgraph {from=pos, to=pos+1})
                       | Tigerassem.MOVE {assem=assem, dest=dest, src=src} =>
                             (case is of
                                   [] => cgraph
                                 | x::xs => mk_edge cgraph {from=pos, to=pos+1})
                in  genEdges cgraph' is (pos+1)
                end

        fun genMoves moveTab [] _ = moveTab
          | genMoves moveTab (i::is) pos =
                let val boolMove = case i of 
                                        Tigerassem.MOVE _ => true
                                      | _      => false
                in  genMoves (tabInserta(pos, boolMove, moveTab)) is (pos+1)
                end

        fun genDefUse (defT, useT) [] _ = (defT, useT)
          | genDefUse (defT, useT) (i::is) pos =
                let val (dest, src) = case i of
                                             Tigerassem.OPER {dest=dest, src=src, ...} => (dest, src)
                                           | Tigerassem.LABEL _ => ([], [])
                                           | Tigerassem.MOVE {dest=dest, src=src, ...} => (dest, src)
                    val defT' = tabInserta(pos, dest, defT)
                    val useT' = tabInserta(pos, src, useT)
                in  genDefUse (defT', useT') is (pos+1)
                end

        fun genEdgesbyBlock (is, (ctrl, n)) = (genEdges ctrl is n, n + List.length is)

        val (control', _) = List.foldl genEdgesbyBlock (control, 0) (List.map List.rev instrsblocks)

        val (def', use') = genDefUse (def, use) instrs 0

        val ismove' = genMoves isMove instrs 0

    in  FGRAPH {control = control',
                def = def',
                use = use',
                ismove = ismove',
                nodes = nodes}
    end

fun getMove n (FGRAPH fgraph) =
	let val i = tabSaca (n, (#nodes fgraph))
		in  case i of
				 Tigerassem.MOVE m => ((hd o #dest) m, (hd o #src) m)
			   | _ => raise Fail "getMove: imposible!"
		end

end
