structure Tigerextras =
struct

fun unionsinrep [] ys = ys
  | unionsinrep xs [] = xs
  | unionsinrep (x::xs) ys = let fun eq z = (x = z)
                                 val exist = List.exists eq ys
                             in  if exist then unionsinrep xs ys else x::(unionsinrep xs ys)
                             end

(* restadelist a b = a - b en conjuntos *)
fun restadelist xs ys = 
    List.foldr (fn (y, xs') => List.filter (fn x => x <> y) xs') xs ys

fun list2set xs = Splayset.addList ((Splayset.empty String.compare), xs)

end
