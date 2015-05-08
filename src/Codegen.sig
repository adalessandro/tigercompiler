signature Codegen =
sig

    val munchStmBlock : Tree.stm list * Frame.frame -> Assem.instr list

	val replace : Assem.temp * Assem.reg -> Assem.instr -> Assem.instr

    val ilist : Assem.instr list ref
    
end
