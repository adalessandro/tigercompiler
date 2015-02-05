signature Tigertemp = sig
	type label = string
	type temp = string
	val makeString: string -> string
	val newtemp: unit -> temp
	val newlabel: unit -> label
    val getTempNum: temp -> int
    val getTempName: int -> temp
end
