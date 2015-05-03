signature Graph =
sig

	structure Set : Splayset
    
	type graph
    type node = int

    val nodes : graph -> node Set.set
    val succ : graph -> node -> node Set.set
    val pred : graph -> node -> node Set.set
    val adj : graph -> node -> node Set.set
    val eq : node * node -> bool

    val newGraph : unit -> graph
    val newNode : graph -> node -> graph
    val newNodes : graph -> node list -> graph
    exception GraphEdge
    val mk_edge : graph -> {from: node, to: node} -> graph
    val rm_edge : graph -> {from: node, to: node} -> graph
    val areAdj : graph -> node -> node -> bool

    type 'a table = (node, 'a) Tab.Tabla

    val nodename : node -> string
    
    val printSet : ('a -> unit) -> 'a Set.set -> unit 
    val printGraph : (node -> unit) -> graph -> unit 

    val entry2pp : string -> unit
    val entrypp : node * string list -> unit
    val entryppbool : node * bool -> unit
end
