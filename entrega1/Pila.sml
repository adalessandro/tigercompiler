structure Pila :> Pila =
struct

type 'a Pila = 'a list ref

fun nuevaPila () = ref []

fun nuevaPila1 e = ref [e]

fun pushPila pila item = pila := (item :: (!pila))

fun popPila pila =
        let val ret = hd (!pila)
        in 
            pila := tl (!pila);
            ret
        end

fun topPila pila = hd (!pila)

fun toList pila = (!pila)

fun isEmpty pila = List.null (!pila)

end
