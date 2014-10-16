structure Tigersres =
struct

open Tigerabs
open Tigertab
open Tigertips

datatype EnvEntry =
    Var of {ty: Tipo}
  | Func of {level: unit, label: Tigertemp.label,
        formals: Tipo list, result: Tipo, extern: bool}

val mainLevel = ()

end
