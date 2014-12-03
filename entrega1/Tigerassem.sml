structure Tigerassem :> Tigerassem =
struct

open Tigertree

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
    
fun format f i = ""

fun munchStm s = ()

fun munchExp e = "t"

end
