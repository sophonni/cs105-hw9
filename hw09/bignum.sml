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
            |   GREATER => NEG (x /-/ y)
            |   LESS => POS (y /-/ x)
            )
        |   (NEG x) <+> (NEG y) = NEG (x /+/ y)
        |   (NEG x) <+> ZERO = NEG x
        |   (POS x) <+> (POS y) =   POS (x /+/ y)
        |   (POS x) <+> (NEG y) =
            (case (N.compare (x, y))
            of  EQUAL => ZERO
            |   GREATER => POS (x /-/ y)
            |   LESS => NEG (y /-/ x)
            )
        |   (POS x) <+> ZERO = (POS x)
        |   ZERO <+> (POS y) = (POS y)
        |   ZERO <+> (NEG y) = NEG y
        |   ZERO <+> ZERO = ZERO



        fun (NEG x) <-> (POS y) =
            (case (N.compare (x, y))
            of  EQUAL => ZERO
            |   _ => NEG (x /+/ y)
            )
        |   (NEG x) <-> (NEG y) =
            (case (N.compare (x, y))
            of  EQUAL => ZERO
            |   LESS => POS (y /-/ x)
            |   GREATER => NEG (x /-/ y)
            )
        |   (NEG x) <-> ZERO = NEG x
        |   (POS x) <-> (POS y) =
            (case (N.compare (x, y))
                of  EQUAL => ZERO
                |   LESS => NEG (y /-/ x)
                |   GREATER => POS (x /-/ y)
            )
        |   (POS x) <-> (NEG y) = POS (x /+/ y)
        |   (POS x) <-> ZERO = (POS x)
        |   ZERO <-> (POS y) = NEG y
        |   ZERO <-> (NEG y) = (POS y)
        |   ZERO <-> ZERO = ZERO



        (* (case (N.compare (x, y))
        of  EQUAL =>
        |   LESS => 
        |   GREATER => 
        ) *)
        fun (NEG x) <*> (POS y) = NEG (x /*/ y)
        |   (NEG x) <*> (NEG y) = POS (x /*/ y)
        |   (NEG x) <*> ZERO = ZERO

        |   (POS x) <*> (POS y) = POS (x /*/ y)
        |   (POS x) <*> (NEG y) = NEG (x /*/ y)
        |   (POS x) <*> ZERO = ZERO

        |   ZERO <*> (POS y) = ZERO
        |   ZERO <*> (NEG y) = ZERO
        |   ZERO <*> ZERO = ZERO

        fun compare (NEG x, POS y) = LESS
        |   compare (NEG x, NEG y) = N.compare (y, x)
        |   compare (NEG x, ZERO) = LESS

        |   compare (POS x, POS y) = N.compare (x, y)
        |   compare (POS x, NEG y) = GREATER
        |   compare (POS x, ZERO) = GREATER

        |   compare (ZER0, POS y) = LESS
        |   compare (ZER0, NEG y) = GREATER
        |   compare (_, _) = EQUAL


        fun (POS x) sdiv c =
            let
                val { quotient = q, remainder = r } = N.sdiv (x, c)
            in
                { quotient = POS q, remainder = r }
            end
        |   _ sdiv c = raise LeftAsExercise


        fun toStringHelper x =
            let
                val arrayOfDigit = N.decimal x
                val toConcat = (fn (x, accum) => Int.toString x ^ accum)
                val resultingStr = foldr toConcat "" arrayOfDigit
            in
                resultingStr
            end


        fun toString (POS x) = toStringHelper x
        |   toString (NEG x) = "-" ^ toStringHelper x
        |   toString ZER0 = "0" 

    end