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

(*
        val t = tabNueva ()
        val t' = List.foldr (fn ((tab, n), ins) => (tabInserta (n, ins, tab), n+1)) (t, 0) instrs
*)
fun makeFGraph (instrsblocks:(Tigerassem.instr list list)) =
    let val instrs = (List.concat o List.map List.rev) instrsblocks
        val _ = (print o Tigerassem.assemblock2str) instrs
        val nodes = #1 (List.foldr (fn (i, (t, n)) => (tabInserta (n, i, t),  n+1)) (tabNueva(), 0) instrs)
        val control = #1 (List.foldr (fn (_, (gra, n)) => (newNode gra n,  n+1)) (newGraph(), 0) instrs)
        val def = tabNueva ()
        val use = tabNueva ()
        val isMove = tabNueva ()
        fun jumppp NONE = "jump = NONE"
          | jumppp (SOME [x]) = "jump = [" ^ x ^ "]"
          | jumppp (SOME [x, y]) = "jump = [" ^ x ^ ", " ^ y ^ "]"
        fun genEdges cgraph [] _ = cgraph
          | genEdges cgraph (i::is) pos = 
                let val cgraph' = 
                    case i of
                         Tigerassem.OPER {assem=assem, dest=dest, src=src, jump=jump} =>
                             (case jump of
                                   NONE => (case is of
                                                 [] => cgraph
                                               | x::xs => mk_edge cgraph {from=pos, to=pos+1})
                                 | SOME [l] => let val labpos = Tigerassem.labelpos l instrs 0
                                               in (case labpos of
                                                        NONE => raise Fail "makeFGraph: label no encontrada"
                                                      | SOME p => mk_edge cgraph {from=pos, to=p})
                                               end
                                 | SOME [l, "FALSE_LABEL"] => let val labpos = Tigerassem.labelpos l instrs 0
                                                                val cgnext = mk_edge cgraph {from=pos, to=pos+1}
                                                            in (case labpos of
                                                                     NONE => raise Fail "makeFGraph: label no encontrada"
                                                                   | SOME p => mk_edge cgnext {from=pos, to=p})
                                                            end
                                 | _ => raise Fail "makeFGraph: jump malformado")
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
        val (def', use') = genDefUse (def, use) instrs 0
    in  FGRAPH {control = genEdges control instrs 0,
                def = def',
                use = use',
                ismove = genMoves isMove instrs 0,
                nodes = nodes}
    end

val ej1 = [
    Tigerassem.OPER {assem="", dest=[], src=[], jump=NONE},
    Tigerassem.LABEL{assem="", lab="l1"},
    Tigerassem.OPER {assem="", dest=[], src=[], jump=NONE},
    Tigerassem.OPER {assem="", dest=[], src=[], jump=NONE},
    Tigerassem.OPER {assem="", dest=[], src=[], jump=NONE},
    Tigerassem.OPER {assem="", dest=[], src=[], jump=SOME["l1", "DEF_LABEL"]},
    Tigerassem.OPER {assem="", dest=[], src=[], jump=NONE}
    ]

end
