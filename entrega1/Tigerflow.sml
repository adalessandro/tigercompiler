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
fun makeFGraph (instrs:(Tigerassem.instr list)) =
    let val control = #1 (List.foldr (fn (_, (gra, n)) => (newNode gra n,  n+1)) (newGraph(), 0) instrs)
        val def = Tigertab.tabNueva ()
        val use = Tigertab.tabNueva ()
        val isMove = Tigertab.tabNueva ()
        fun genEdges cgraph [] _ = cgraph
          | genEdges cgraph (i::is) pos = 
                let val cgraph' = 
                    case i of
                         Tigerassem.OPER {assem=assem, dest=dest, src=src, jump=jump} =>
                             (case jump of
                                   NONE => (case is of
                                                 [] => cgraph
                                               | x::xs => mk_edge cgraph {from=pos, to=pos+1})
                                 | SOME [l] => let val labpos = Tigerassem.labelpos l instrs
                                               in (case labpos of
                                                        NONE => raise Fail "makeFGraph: label no encontrada"
                                                      | SOME p => mk_edge cgraph {from=pos, to=p})
                                               end
                                 | SOME [l, "DEF_LABEL"] => let val labpos = Tigerassem.labelpos l instrs
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
    in  Tigergraph.printGraph (genEdges control instrs 0)
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
