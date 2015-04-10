signature Tigerpila =
sig

type 'a Pila
val nuevaPila : unit -> 'a Pila
val nuevaPila1 : 'a -> 'a Pila
val pushPila : 'a Pila -> 'a -> unit
val popPila : 'a Pila -> unit
val topPila : 'a Pila -> 'a
val toList : 'a Pila -> 'a list
val isEmpty : 'a Pila -> bool

end
