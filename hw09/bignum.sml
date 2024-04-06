functor BignumFn(structure N : NATURAL) : BIGNUM =
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

        fun (NEG x) <+> (POS y) =
            (case (N.compare (x, y))
            of  EQUAL => ZERO
            (* big negative + small positive = negative. Thus,
            raise exception *)
            |   GREATER => raise N.Negative
            |   LESS => POS (y /-/ x)
            )
        (* negative + negative = negative. Thus, raise exception *)
        |   (NEG x) <+> (NEG y) = raise N.Negative
        |   (NEG x) <+> ZERO = raise N.Negative
        |   (POS x) <+> (POS y) =   POS (x /+/ y)
        |   (POS x) <+> (NEG y) =
            (case (N.compare (x, y))
            of  EQUAL => ZERO
            |   GREATER => POS (x /-/ y)
                (* small positive + big negative = negative. Thus,
                raise exception *)
            |   LESS => raise N.Negative
            )
        |   (POS x) <+> ZERO = (POS x)
        |   ZERO <+> (POS y) = (POS y)
        (* 0 + negative = negative. Thus, raise exception *)
        |   ZERO <+> (NEG y) = raise N.Negative
        |   ZERO <+> ZERO = ZERO



            (* (case (N.compare (x, y))
            of  EQUAL =>
            |   LESS => 
            |   GREATER => 
            ) *)

        fun (NEG x) <-> (POS y) =
            (case (N.compare (x, y))
            of  EQUAL => ZERO
                (* negative - any positive = negative. Thus, raise exception *)
            |   _ => raise N.Negative
            )
        |   (NEG x) <-> (NEG y) =
            (case (N.compare (x, y))
            of  EQUAL => ZERO
            |   LESS => POS (y /-/ x)
                (* big negative - small negative = negative. Thus, raise exception *)
            |   GREATER => raise N.Negative
            )
        |   (NEG x) <-> ZERO = raise N.Negative
        |   (POS x) <-> (POS y) =
            (case (N.compare (x, y))
                of  EQUAL => ZERO
                |   LESS => raise N.Negative
                |   GREATER => POS (x /-/ y)
            )
        |   (POS x) <-> (NEG y) = POS (x /+/ y)
        |   (POS x) <-> ZERO = (POS x)
        |   ZERO <-> (POS y) = raise N.Negative
        |   ZERO <-> (NEG y) = (POS y)
        |   ZERO <-> ZERO = ZERO

        fun x <*> y = raise LeftAsExercise
        fun compare (x, y) = raise LeftAsExercise
        fun bigInt sdiv c = raise LeftAsExercise
        fun toString bigInt = raise LeftAsExercise

    end