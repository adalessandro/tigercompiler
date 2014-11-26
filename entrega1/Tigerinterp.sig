signature Tigerinterp =
sig
 
val inter : bool -> ((Tigertree.stm list*Tigerframe.frame) list) -> ((Tigertemp.label*string) list)-> unit

end
