signature Frame =
sig

(* Type Definitions *)
type frame
type register = string

datatype access =
		InFrame of int
	  | InReg of Temp.label
datatype frag =
		PROC of {body: Tree.stm, frame: frame}
	  | STRING of Temp.label * string
datatype canonfrag =
		CPROC of {body: Tree.stm list, frame: frame}
      | CSTRING of Temp.label * string


(* Architecture Regs and Machine Dependent Constants *)
val rv : Temp.temp
val fp : Temp.temp
val sp : Temp.temp
val pc : Temp.temp
val lr : Temp.temp

val fpPrev : int
val fpPrevLev : int
val wSz : int
val specialregs : Temp.temp list
val argregs : Temp.temp list
val argregslen : int
val generalregs : Temp.temp list
val genregslen : int
val calleesaves : Temp.temp list
val callersaves : Temp.temp list

(* Frame Functions *)
val newFrame : {name: Temp.label, escapes: bool list} -> frame
val name : frame -> Temp.label
val makeString : Temp.label * string -> string
val formals : frame -> access list
val allocArg : frame -> bool -> access
val allocLocal : frame -> bool -> access
val maxRegFrame : frame -> int
val exp : access -> Tree.exp
val externalCall : string * Tree.exp list -> Tree.exp

(* ProcEntryExit *)
val procEntryExit1:
		frame * Tree.stm -> Tree.stm
val procEntryExit2:
		frame * Assem.instr list -> Assem.instr list
val procEntryExit3 :
		frame * Assem.instr list -> {prolog: string, body: Assem.instr list, epilog: string}

(* Extras *)
val frag2str : frag -> string
val printfrag : frag -> unit
val canonfrag2str : canonfrag -> string
val printcanonfrag : canonfrag -> unit
val printFrame : frame -> unit

end
