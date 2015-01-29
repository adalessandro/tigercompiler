signature Tigergraph =
sig
    type graph
    type node

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

    type 'a table

    val nodename : node -> string
end
