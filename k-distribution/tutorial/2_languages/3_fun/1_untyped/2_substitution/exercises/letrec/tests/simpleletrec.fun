
letrec f = fun x -> 1 and
       g = fun x -> (f x)
       in (g 7)