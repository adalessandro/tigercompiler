structure Assem :> Assem =
struct

open Tigerextras

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
   
val FALSE_LABEL = "__FALSE_LABEL__"
val RET_LABEL = "__RET_LABEL__"
val CALL_LABEL = "__CALL_LABEL__" 

fun const i = "#" ^ Int.toString(i)
fun flabel l = "=" ^ l

(* ----- Extras ----- *)
fun getTemps instr =
        case instr of
        OPER {dest = dest, src = src, ...} => dest @ src
      | LABEL _ => []
      | MOVE {dest = dest, src = src, ...} => dest @ src

fun labelpos x [] = raise Fail ("labelpos: label " ^ x ^ "not found")
  | labelpos x (LABEL {lab=lab, ...} :: ys) =
            if lab = x then 0 else 1 + labelpos x ys
  | labelpos x (_ :: ys) = 1 + labelpos x ys

val format =
    let fun speak(assem, dst, src, jump) =
            let fun get_elem ls i = List.nth (ls, ord i - ord #"0")
                fun saylab s = s 
                fun saytemp t = t 
                fun f(#"`" :: #"s" :: i ::rest) = 
                        (saytemp o get_elem src) i ^ f rest
                  | f( #"`":: #"d":: i:: rest) = 
                        (saytemp o get_elem dst) i ^ f rest
                  | f( #"`":: #"j":: i:: rest) = 
                        (saylab o get_elem jump) i ^ f rest
                  | f( #"`":: _ :: rest) = raise Fail "bad Assem format"
                  | f(c :: rest) = (str c ^ f rest)
                  | f nil = "" 
            in (f o explode) assem
            end 
    in fn OPER {assem, dest, src, jump=NONE} => speak("\t" ^ assem, dest, src, nil)
        | OPER {assem, dest, src, jump=SOME j} => speak("\t" ^ assem, dest, src, j)
        | LABEL {assem, ...} => assem
        | MOVE {assem, dest, src} => speak("\t" ^ assem, dest, src, nil)
    end

fun strAssem i = format i ^ "\n"

fun printAssem i = (print o strAssem) i

end
