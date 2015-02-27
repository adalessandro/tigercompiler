signature Tigerframe =
sig

type frame
val printFrame : frame -> unit
type register = string
val rv : Tigertemp.temp
val fp : Tigertemp.temp
datatype access = InFrame of int | InReg of Tigertemp.label
val fpPrev : int
val fpPrevLev : int
val newFrame : {name: Tigertemp.label, formals: bool list} -> frame
val name : frame -> Tigertemp.label
val string : Tigertemp.label * string -> string
val formals : frame -> access list
val allocArg : frame -> bool -> access
val allocLocal : frame -> bool -> access
val sp : Tigertemp.temp
val maxRegFrame : frame -> int
val wSz : int
val log2WSz : int
val calldefs : Tigertemp.temp list
val specialregs : Tigertemp.temp list
val argregs : Tigertemp.temp list
val argregslen : int
val callersaves : Tigertemp.temp list
val generalregs : Tigertemp.temp list
val exp : access -> Tigertree.exp
val externalCall : string * Tigertree.exp list -> Tigertree.exp
val procEntryExit1 : frame * Tigertree.stm -> Tigertree.stm
(*val procEntryExit2 : frame * Tigerassem.instr list -> Tigerassem.instr list*)
datatype frag = PROC of {body: Tigertree.stm, frame: frame}
	| STRING of Tigertemp.label * string
val frag2str : frag -> string
datatype canonfrag = CPROC of {body: Tigertree.stm list, frame: frame}
    | CSTRING of Tigertemp.label * string
val canonfrag2str : canonfrag -> string
end
