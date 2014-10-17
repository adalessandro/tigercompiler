signature Topsort =
sig
    val fijaTipos : {name: Tigerabs.symbol, ty: Tigerabs.ty} list -> (string, Tigertips.Tipo) Tigertab.Tabla -> (string, Tigertips.Tipo) Tigertab.Tabla
    exception Ciclo
end
