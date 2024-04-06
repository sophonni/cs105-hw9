functor BignumFn(structure N : NATURAL) :> BIGNUM =
    struct
        datatype bigint = POS of N.nat
                        | NEG of N.nat
                        | ZERO

        infix 6 <+> <->
        infix 7 <*> sdiv
        val /+/ = N./+/
        val /-/ = N./-/
        val /*/ = N./*/
        infix 6 /+/ /-/
        infix 7 /*/

        exception Negative    (* raised if any operation's result would be negative *)
        exception BadDivision
        exception LeftAsExercise

        fun ofInt intVal =  if (intVal < 0) then
                                let
                                    val addOne = intVal
                                    val negatedSum = addOne * (~1)
                                    val negatedNat = N.ofInt negatedSum
                                in
                                    NEG negatedNat
                                end
                            else
                                if (intVal = 0) then
                                    ZERO
                                else
                                    POS (N.ofInt intVal)


        fun negated (POS n) = NEG n
        |   negated (NEG n) = POS n
        |   negated ZERO = ZERO

        fun x <+> y = raise LeftAsExercise
        fun x <-> y = raise LeftAsExercise
        fun x <*> y = raise LeftAsExercise
        fun compare (x, y) = raise LeftAsExercise
        fun bigInt sdiv c = raise LeftAsExercise
        fun toString bigInt = raise LeftAsExercise

    end