structure CantPrints :> CantPrints =
struct

open Tigerabs

(* cantPrintsExpr: dado un tigerabs.exp devuelve la cantidad de llamadas a la
función print cuyo argumento no es un StringExp.*)
fun cantPrintsExpr (VarExp(var, _)) = cantPrintsVar var 
  | cantPrintsExpr (UnitExp(_)) = 0
  | cantPrintsExpr (NilExp(_)) = 0
  | cantPrintsExpr (IntExp(_, _)) = 0
  | cantPrintsExpr (StringExp(_, _)) = 0
  | cantPrintsExpr (CallExp({func, args}, _)) = (
        case (func, args) of
            ("print", [StringExp(_, _)]) => 1
          | (_, _) => 0
        )
  | cantPrintsExpr (OpExp({left, oper=_, right}, pos)) = cantPrintsExpr left + cantPrintsExpr right
  | cantPrintsExpr (RecordExp({fields, typ=_}, _)) = foldr (fn(x,n) => cantPrintsExpr(#2(x)) + n) 0 fields
  | cantPrintsExpr (SeqExp(exps, _)) = foldr(fn(x,n) => cantPrintsExpr x + n) 0 exps
  | cantPrintsExpr (AssignExp({var=_, exp}, _)) = cantPrintsExpr exp
  | cantPrintsExpr (IfExp({test, then', else'}, pos)) = (
        case else' of
            NONE => cantPrintsExpr test + cantPrintsExpr then'
          | SOME e => cantPrintsExpr test + cantPrintsExpr then' + cantPrintsExpr e
        )
  | cantPrintsExpr (WhileExp({test, body}, _)) = cantPrintsExpr test + cantPrintsExpr body
  | cantPrintsExpr (ForExp({var=_, escape=_, lo, hi, body}, _)) =
        cantPrintsExpr lo + cantPrintsExpr hi + cantPrintsExpr body
  | cantPrintsExpr (LetExp({decs, body}, _)) =
        foldr (fn(x, n) => cantPrintsDec x + n) 0 decs + cantPrintsExpr body
  | cantPrintsExpr (BreakExp(_)) = 0
  | cantPrintsExpr (ArrayExp({typ=_, size=_, init=_}, _)) = 0

(* cantPrintsVar: dado un tigerabs.var devuelve la cantidad de llamadas a la
función print cuyo argumento no es un StringExp.*)
and cantPrintsVar (SimpleVar(_)) = 0
  | cantPrintsVar (FieldVar(var, _)) = cantPrintsVar var 
  | cantPrintsVar (SubscriptVar(var, exp)) = cantPrintsVar var + cantPrintsExpr exp

(* cantPrintsDec: dado un tigerabs.dec devuelve la cantidad de llamadas a la
función print cuyo argumento no es un StringExp.*)
and cantPrintsDec (FunctionDec(funcDecs)) = 
        foldr (fn(x, n) => cantPrintsExpr(#body(#1(x))) + n) 0 funcDecs
  | cantPrintsDec (VarDec({name=_, escape=_, typ=_, init=varInit}, _)) = cantPrintsExpr varInit
  | cantPrintsDec (TypeDec(_)) = 0

end

