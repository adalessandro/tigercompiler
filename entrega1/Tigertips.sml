structure Tigertips =
struct

type unique = unit ref

datatype R = RO | RW (* read-only para el índice del for *)

datatype Tipo = TUnit
    | TNil
    | TInt of R (* read-only | read-write *)
    | TString
    | TArray of Tipo * unique
    | TRecord of (string * Tipo * int) list * unique (* nombre, tipo, posición *)
    | TFunc of Tipo list * Tipo (* tipo argumentos, tipo retorno *)
    | TTipo of string * Tipo option ref (* por qué option? *)

fun printTipo TUnit = "TUnit"
  | printTipo TNil = "TNil"
  | printTipo (TInt RO) = "TInt RO"
  | printTipo (TInt RW) = "TInt RW"
  | printTipo TString = "TString"
  | printTipo (TArray (t,_)) = "TArray("^printTipo t^")"
  | printTipo (TRecord (l,_)) = "TRec("^printFields l^")"
  | printTipo (TFunc _) = "TFunc(...)"
  | printTipo (TTipo(s,ref NONE)) = "TTipo("^s^",NONE!!!!)"
  (*| printTipo (TTipo(s,ref (SOME x))) = "TTipo("^s^","^printTipo x^")"*)
  | printTipo (TTipo(s,ref (SOME x))) = "TTipo("^s^","^"SOMEEE"^")"

and printFields l = List.foldl (fn(x,y) => x^", "^y) "" (map (fn(a,b,i)=>a^":"^printTipo b^" ("^makestring(i)^")") l)

end
