signature Assem =
sig
    type reg = string
    type temp = Temp.temp
    type label = Temp.label

    datatype instr =
        OPER of {assem: string,
                 dest: temp list,
                 src: temp list,
                 jump: label list option}
      | LABEL of {assem: string,
                  lab: label}
      | MOVE of {assem: string,
                 dest: temp list,
                 src: temp list}

    val ilist : instr list ref
    
    (*val format : (temp -> string) -> instr -> string*)
    val format : instr -> string

	val printAssem : instr -> unit

    val munchStmBlock : Tree.stm list * Frame.frame -> instr list

    val labelpos : label -> instr list -> int

	val getTemps : instr -> temp list
	
	val replace : temp * reg -> instr -> instr

    val FALSE_LABEL : label
    val RET_LABEL : label
    val CALL_LABEL : label

end
