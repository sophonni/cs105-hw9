functor BignumFn(structure N : NATURAL) : BIGNUM =
    struct
        (*  A 'bigint' is either 0, a negative natural number, or a
        *   positive natural number. The representation of the ntural
        *   number is of similar representation as 'N.nat'. However,
        *   'bigint' datatype is used implement signed, arbitrary-precision
        *   integers.

        *
        *  Invariants of 'bigint' Representation:
        *   In values of the form ZERO,
        *     - there are no invariants to maintain

        *   In values of the form 'POS of N.nat',
        *       - follows the same invariant as N.nat where the only
        *       difference is this type constructor is used to represents
        *       positive natural numbers
        
        *   In values of the form 'NEG of N.nat',
        *       - follows the same invariant as N.nat where the only
        *       difference is this type constructor is used to represents
        *       negative natural numbers
        *)
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

        exception Negative
        exception BadDivision

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
        |   (NEG x) sdiv c =
            let
                val { quotient = q, remainder = r } = N.sdiv (x, c)
            in
                { quotient = NEG q, remainder = r }
            end
        |   ZERO sdiv c = { quotient = ZERO, remainder = 0 }


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