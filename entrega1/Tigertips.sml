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

end
