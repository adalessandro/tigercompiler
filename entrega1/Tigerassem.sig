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

    val munchStm : Tigertree.stm -> unit
    val munchExp : Tigertree.exp -> temp
end
