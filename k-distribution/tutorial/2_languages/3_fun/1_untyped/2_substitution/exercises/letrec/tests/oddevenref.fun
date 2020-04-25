


let odd = ref 0 and even = ref 0 in (
    (odd := ( fun 0 -> false | n -> (@even (n - 1)) ));
    (even := ( fun 0 -> true | n -> (@odd (n - 1)) )); 
    ((@odd) 5) )