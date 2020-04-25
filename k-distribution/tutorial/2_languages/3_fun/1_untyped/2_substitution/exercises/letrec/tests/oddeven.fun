

letrec odd = fun 0 -> false | n -> (even (n - 1))
    and even = fun 0 -> true | n -> (odd (n - 1)) 
    in (even 5)