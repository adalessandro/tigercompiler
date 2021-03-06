signature Tab =
sig

type ('a, 'b) Tabla
exception yaExiste of string
exception noExiste
exception noExisteS of string
val tabNueva : unit -> (''a, 'b) Tabla
val fromTab : (''a, 'b) Tabla -> (''a, 'b) Tabla
val name : 'a -> 'a
val tabEsta : ''a * (''a, 'b) Tabla -> bool
val tabInserta : ''a * 'b * (''a, 'b) Tabla -> (''a, 'b) Tabla
val tabRInserta : ''a * 'b * (''a, 'b) Tabla -> (''a, 'b) Tabla
val tabRInserta_ : ''a * 'b * (''a, 'b) Tabla ref -> unit
val tabBusca : ''a * (''a, 'b) Tabla -> 'b option
val tabSaca : ''a * (''a, 'b) Tabla -> 'b
val tabAplica : ('a -> 'b) * (''c, 'a) Tabla -> (''c, 'b) Tabla
val tabAAplica : ('a -> ''c) * ('b -> 'd) * ('a, 'b) Tabla -> (''c, 'd) Tabla
val tabRAAplica : ('a -> ''b) * ('c -> 'd) * ('a, 'c) Tabla -> (''b, 'd) Tabla
val tabInserList : ('a, 'b) Tabla * ('a * 'b) list -> ('a, 'b) Tabla
val tabAList : ('a, 'b) Tabla -> ('a * 'b) list
val tabLength : ('a, 'b) Tabla -> int
val tabFiltra : ('b -> bool) * (''a, 'b) Tabla -> (''a, 'b) Tabla
val tabPrimer : ('b -> bool) * ('a, 'b) Tabla -> ('a * 'b)
val tabClaves : ('a, 'b) Tabla -> 'a list
val tabImagen : ('a, 'b) Tabla -> 'b list
val tabEq : ('b * 'b -> bool) -> ('a, 'b) Tabla * ('a, 'b) Tabla -> bool
val tabEqRange : ('a, 'b) Tabla -> ('a, 'c) Tabla -> 'a list -> ('b * 'c -> bool) -> bool
val printTab : ('a -> unit) -> ('b -> unit) -> ('a, 'b) Tabla -> unit

end
