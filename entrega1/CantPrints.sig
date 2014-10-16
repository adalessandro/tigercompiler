signature CantPrints =
sig
    val cantPrintsExpr: Tigerabs.exp -> int
    val cantPrintsVar: Tigerabs.var -> int
    val cantPrintsDec: Tigerabs.dec -> int
end
