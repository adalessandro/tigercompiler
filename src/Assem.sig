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

    val format : instr -> string

	val strAssem : instr -> string

	val printAssem : instr -> unit

    val labelpos : label -> instr list -> int

	val getTemps : instr -> temp list
	
    val FALSE_LABEL : label
    val RET_LABEL : label
    val CALL_LABEL : label

	val constlist : (string * int) list ref
	val emitConst : int -> label

	val const : int -> string
	val flabel : string -> string

end
