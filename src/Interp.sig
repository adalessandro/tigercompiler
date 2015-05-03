signature Interp =
sig
 
val inter : bool -> ((Tree.stm list*Frame.frame) list) -> ((Temp.label*string) list)-> unit

end
