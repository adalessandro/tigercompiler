fun foldr _ i [] = i
       | f i (h::T) = f(h, foldr f i t)

foldr opt 0 [1,2,3,4,5]
foldr (fn(x,n) => cantprints x + n) 0 lista
