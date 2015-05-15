signature Codegen =
sig
	val replace : Assem.temp * Assem.reg -> Assem.instr -> Assem.instr
    val codegen : (Tree.stm list * Frame.frame) list -> Assem.instr list list
	val genConst : int * Assem.temp -> string option
end
