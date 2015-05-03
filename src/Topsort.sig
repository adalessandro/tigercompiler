signature Topsort =
sig
    val fijaTipos : {name: Abs.symbol, ty: Abs.ty} list -> (string, Tips.Tipo) Tab.Tabla -> (string, Tips.Tipo) Tab.Tabla
    exception Ciclo
end
