(* Starter code for Exercise 1 of Modules assignement.
*  Authors: Kell Pogue and Norman Ramsey (edits by Richard Townsend) *) 

structure GNatural : NATURAL = struct
  (* A nat is either 0 or (m * d), where m is a nat and d is a digit.
  *
  *  Invariants on our representation:
  *   In values of the form ZERO,
  *     - there are no invariants to maintain
  *   In values of the form TIMESBASEPLUS (n, d),
  *     - n and d cannot both be zero
  *     - d must be a machine integer in the range 0 <= d < base
  *     - n must follow our invariants
  *)
  datatype nat = ZERO
               | TIMESBASEPLUS of nat * int

  val base = 0x8000

  (* constructs nat values that preserve first invariant *)
  fun timesBasePlus (ZERO, 0) = ZERO
    | timesBasePlus (n, d) = TIMESBASEPLUS (n, d)

  exception Negative    (* raised if any operation's result would be negative *)

  exception BadDivisor

  (* converts a nonnegative machine integer into a natural number *)
  fun ofInt 0 = ZERO
    | ofInt n = timesBasePlus (ofInt (n div base), n mod base)

  infix 6 /+/ /-/
  infix 7 /*/ sdiv


  (* carryIntoNat (n, c) adds natural number n to carry bit c. A carry bit is a
  *  machine integer that is either 0 or 1. It raises exception Match if
  *  provided an invalid carry bit.
  *)
  fun carryIntoNat (n, 0) = n
    | carryIntoNat (ZERO, 1) = timesBasePlus (ZERO, 1)
    | carryIntoNat (TIMESBASEPLUS (m, d), 1) =
        timesBasePlus (carryIntoNat (m, (d + 1) div base), (d + 1) mod base)
    | carryIntoNat _  = raise Match (* bad carry bit *)

  (* addWithCarry (n1, n2, c) takes natural numbers n1 and n2 and carry bit c,
  *  and returns n1 + n2 + c.
  *)
  fun addWithCarry (x, ZERO, c) = carryIntoNat (x, c)
    | addWithCarry (ZERO, y, c) = carryIntoNat (y, c)
    | addWithCarry (TIMESBASEPLUS (m1, d1), TIMESBASEPLUS (m2, d2), c) =
        let val d  = (d1 + d2 + c) mod base
            val c' = (d1 + d2 + c) div base (* the "carry out" *)
        in  timesBasePlus (addWithCarry (m1, m2, c'), d)
        end

  (* Addition on two natural numbers x and y *)
  fun x /+/ y = addWithCarry (x, y, 0)

  (* borrowFromNat (n, b) takes a natural number n and a borrow bit b and
  * returns n - b, provided that that difference is a natural number. If not,
  * the function raises exception Negative. It raises exception Match given an
  * invalid borrow bit.
  *)
  fun borrowFromNat (n, 0) = n
    | borrowFromNat (TIMESBASEPLUS (m, 0), 1) =
        timesBasePlus (borrowFromNat (m, 1), base - 1)
    | borrowFromNat (TIMESBASEPLUS (m, d), 1) =
        timesBasePlus (m, d - 1)
    | borrowFromNat (ZERO, 1) = raise Negative
    | borrowFromNat _         = raise Match (* bad carry bit *)

  (* Given natural numbers n1 and n2 and borrow bit b, return n1 - n2 - b if
  *  that difference is a natural number. Otherwise raise exception Negative.
  *)
  fun subWithBorrow (x, ZERO, b) = borrowFromNat (x, b)
    | subWithBorrow (TIMESBASEPLUS (m1, d1), TIMESBASEPLUS (m2, d2), b) =
        let val d = (d1 - d2 - b) mod base
            val b' = if d1 - d2 - b < 0 then 1 else 0
        in  timesBasePlus (subWithBorrow (m1, m2, b'), d)
        end
    | subWithBorrow (ZERO, TIMESBASEPLUS _, b) = raise Negative

  (* Subtraction on two natural numbers x and y *)
  fun x /-/ y = subWithBorrow (x, y, 0)

  (* Helper function to clean up construction of natural numbers 
  *  of the form x * base + 0
  *)
  fun timesBase x = timesBasePlus (x, 0)

  (* Multiplication on two natural numbers *)
  fun ZERO /*/ _     = ZERO
    | _    /*/ ZERO  = ZERO
    | (TIMESBASEPLUS (m1, d1)) /*/ (TIMESBASEPLUS (m2, d2)) =
              ofInt (d1 * d2)
          /+/ timesBase (m1 /*/ ofInt d2)
          /+/ timesBase (m2 /*/ ofInt d1)
          /+/ timesBase (timesBase (m1 /*/ m2))

  exception LeftAsExercise

  (* sdiv (n, d) divides natural number n by digit d using short division. 
     The return value is a record of the form
         
       { quotient = q, remainder = r}

     where q and r satisfy these laws:

       n == q /*/ ofInt d /+/ ofInt r
       0 <= r < d

     If d <= 0 or d > base (where "base" is the hidden base selected to
     implement natural numbers), sdiv (n, d) raises BadDivisor.
  *)
  (* m = TIMESBASEPLUS (nat, dec)
    v = digit
    b = base
    d = dec
   *)
  fun ZERO sdiv _ = { quotient = ZERO, remainder = 0 }
    | (TIMESBASEPLUS (nat, dec)) sdiv c =
      if (c <= 0) orelse (c > base) then
        raise BadDivisor
      else
        let
          val { quotient = q, remainder = r} = nat sdiv c
          val intVers = ((r * base) + dec) div c
          val q' = timesBase q /+/ (ofInt intVers)
          val r' = ((r * base) + dec) mod c
        in
          { quotient = q', remainder = r' }
        end

(* SD NOTE: BOTTOM IS WHAT TYPE IT WANTS, TOP IS WHAT TYPE IT'S CURRENTLY IS *)
  (*
   *  Function: compare
   *  Purpose: Given a two natural numbers say 'n1' and 'n2', compare the
   *          two natural numbers return value comparison value that
   *          follows these laws:
   *            - 'GREATER' if 'n1 > n2'
   *            - 'LESS' if 'n1 < n2'
   *            - 'EQUAL' if 'n1 = n2'
  *)
  fun compare (ZERO, ZERO) = EQUAL
    | compare (TIMESBASEPLUS (nat, dec), ZERO) = GREATER
    | compare (ZERO, TIMESBASEPLUS (nat, dec)) = LESS
    | compare (TIMESBASEPLUS (nat1, dec1), TIMESBASEPLUS (nat2, dec2)) =
      (*  if the natural numbers are equal, it's possible that their
          decimal aren't *)
      if nat1 = nat2 then
        
        (*  case when both the natural numbers and their decimals are
            the exact same *)
        if dec1 = dec2 then
          EQUAL
        else

          (*  case when the natural numbers are the same, but their decimal
              of n1 < decimal of n2 *)
          if dec1 < dec2 then
            LESS

          (*  case when the natural numbers are the same, but their
              decimal of n2 < decimal of n1 *)
          else
            GREATER
      
      (*  case when the natural numbers are different, thus we need to
          recursively check the naturals numbers and their decimals *)
      else
        compare (nat1, nat2)

  (*  Function: reverse_decimals
   *  Purpose:  Given a natural number, convert the natural number into
              base-10 and return a list consist of digits of the base-10
              representation of the natural number, in reverse order.
  *)
  fun reverse_decimals ZERO = []
    | reverse_decimals (TIMESBASEPLUS (nat, dec)) = 
      let
        val { quotient = q, remainder = r } =
              (TIMESBASEPLUS (nat, dec)) sdiv 10
      in
        r :: reverse_decimals q
      end

  (*  Function: 
   *  Purpose: given a natural number 'n', returns a list giving the
   *          natural decimal representation of n, most significant digit first.
   *  For example:
   *              decimal (ofInt 123) = [1, 2, 3]
   *              decimal (ofInt 0)   = [0]
   *  Note: this function never returns an empty list, and when it returns a 
   *      list of two or more digits, the first digit is never zero.
  *)
  fun decimal ZERO = [0]
    | decimal (TIMESBASEPLUS (nat, dec)) =
          List.rev (reverse_decimals (TIMESBASEPLUS (nat, dec)))

end

structure Natural :> NATURAL = GNatural
