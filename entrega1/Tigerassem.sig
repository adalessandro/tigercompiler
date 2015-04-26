signature Tigerassem =
sig
    type reg = string
    type temp = Tigertemp.temp
    type label = Tigertemp.label

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

    val assemblock2str : instr list -> string

    val munchStmBlock : Tigertree.stm list * Tigerframe.frame -> instr list

    val labelpos : label -> instr list -> int -> int option

	val getTemps : instr -> temp list

    val FALSE_LABEL : label
    val RET_LABEL : label
    val CALL_LABEL : label

end
