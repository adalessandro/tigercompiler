structure Tigertemp :> Tigertemp =
struct

type label = string
type temp = string

fun makeString s = s

local
    val i = ref 0
    val j = ref 0
in
    fun newtemp() =
        let
            val s = "T"^Int.toString(!i)
        in
            i := !i+1;
            s
        end
    fun newlabel() =
        let
            val s = "L"^Int.toString(!j)
        in
            j := !j+1;
            s
        end
end

fun getTempNum t = case Int.fromString (String.extract (t, 1, NONE)) of
                    NONE => raise Fail "getNum bad val"
                  | SOME x => x

fun getTempName n = "T"^Int.toString(n)

end
