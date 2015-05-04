structure Tigerextras =
struct

fun quitarreps [] = []
  | quitarreps (x::xs) = if List.exists (fn y => x = y) xs then quitarreps xs else x::(quitarreps xs)

fun unionsinrep' [] ys = ys
  | unionsinrep' xs [] = xs
  | unionsinrep' (x::xs) ys = let fun eq z = (x = z)
                                  val exist = List.exists eq ys
                              in  if exist then unionsinrep' xs ys else x::(unionsinrep' xs ys)
                              end

fun unionsinrep xs ys = unionsinrep' (quitarreps xs) (quitarreps ys)

(* restadelist a b = a - b en conjuntos *)
fun restadelist xs ys = 
    List.foldr (fn (y, xs') => List.filter (fn x => x <> y) xs') xs ys

fun list2set xs = Splayset.addList ((Splayset.empty String.compare), xs)

fun listpp f xs = "[" ^ String.concat (List.map (fn x => f x ^ ", ") xs) ^ "]"

fun printlist f xs = (print "["; List.map (fn x => (f x; print ", ")) xs; print "]\n")

fun list_eq ([], []) = true
  | list_eq (x::xs, y::ys) =
        if x = y then list_eq (xs, ys) else false
  | list_eq _ = false

fun pair_compare f g ((a, b), (c, d)) =
        let val x = f (a, c)
        in
            if x = EQUAL then g (b, d) else x
        end

fun printbool true = print "T"
  | printbool false = print "F"

fun printint x = (print o Int.toString) x

end
