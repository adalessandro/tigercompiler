signature Simpleregalloc =
sig
	val simpleregalloc : Temp.temp -> Assem.instr list * Frame.frame -> Assem.instr list * Frame.frame
end
