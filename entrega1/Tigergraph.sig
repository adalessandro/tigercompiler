signature Tigergraph =
sig
    type graph
    type node = int

    val nodes : graph -> node list
    val succ : graph -> node -> node list
    val pred : graph -> node -> node list
    val adj : graph -> node -> node list
    val eq : node * node -> bool

    val newGraph : unit -> graph
    val newNode : graph -> node -> graph
    exception GraphEdge
    val mk_edge : graph -> {from: node, to: node} -> graph
    val rm_edge : graph -> {from: node, to: node} -> graph
    val areAdj : graph -> node -> node -> bool

    type 'a table = (node, 'a) Tigertab.Tabla

    val nodename : node -> string
    
    val printGraph : graph -> unit list

    val entry2pp : string -> unit
    val entrypp : node * string list -> unit
    val entryppbool : node * bool -> unit
end
