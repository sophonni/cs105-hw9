open GNatural

val () =
    Unit.checkExpectWith (Unit.listString Unit.intString) 
    "number conversion 2017"
    (fn () => decimal (ofInt 2017))
    [2, 0, 1, 7]

(* val () =
    Unit.checkExpectWith (Unit.listString Unit.intString) 
    "number conversion 0"
    (fn () => decimal (ofInt 0))
    [0]

val () =
    Unit.checkExpectWith (Unit.listString Unit.intString) 
    "number conversion 123456789"
    (fn () => decimal (ofInt 123456789))
    [1, 2, 3, 4, 5, 6, 7, 8, 9] *)

report