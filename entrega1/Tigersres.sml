structure Tigersres =
struct

open Tigerabs
open Tigertab
open Tigertips

datatype EnvEntry =
    Var of {ty: Tipo}
  | Func of {level: unit, label: Tigertemp.label,
        formals: Tipo list, result: Tipo, extern: bool}

fun envEntry2String (Var{ty}) = "Var of " ^ printTipo ty
  | envEntry2String (Func{formals=formals, result=result, ...}) = 
        "Func of (formals: " ^ formals2String formals ^ "; " ^ (printTipo result) ^ ")"

and formals2String formals = 
        "[" ^ List.foldl (fn(x,y) => x^", "^y) "" (map printTipo formals) ^ "]"

val mainLevel = ()

end
