signature Frame =
sig

type frame
val printFrame : frame -> unit
type register = string
val rv : Temp.temp
val fp : Temp.temp
datatype access = InFrame of int | InReg of Temp.label
val fpPrev : int
val fpPrevLev : int
val newFrame : {name: Temp.label, formals: bool list} -> frame
val name : frame -> Temp.label
val string : Temp.label * string -> string
val formals : frame -> access list
val allocArg : frame -> bool -> access
val allocLocal : frame -> bool -> access
val sp : Temp.temp
val pc : Temp.temp
val lr : Temp.temp
val maxRegFrame : frame -> int
val wSz : int
val log2WSz : int
val calldefs : Temp.temp list
val specialregs : Temp.temp list
val argregs : Temp.temp list
val argregslen : int
val callersaves : Temp.temp list
val generalregs : Temp.temp list
val genregslen : int
val exp : access -> Tree.exp
val externalCall : string * Tree.exp list -> Tree.exp
val procEntryExit1 : frame * Tree.stm -> Tree.stm
(*val procEntryExit2 : frame * Assem.instr list -> Assem.instr list*)
datatype frag = PROC of {body: Tree.stm, frame: frame}
	| STRING of Temp.label * string
val frag2str : frag -> string
val printfrag : frag -> unit
datatype canonfrag = CPROC of {body: Tree.stm list, frame: frame}
    | CSTRING of Temp.label * string
val canonfrag2str : canonfrag -> string
val printcanonfrag : canonfrag -> unit
end
