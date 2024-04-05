
functor PQSortFn(structure Q : PQUEUE) : SORT where type elem = Q.elem =
    struct
        exception LeftAsExercise

        type elem = Q.elem
        type sortedElemList = Q.elem list
        val emptyList = []
        val emptyPQueue = Q.empty
        fun compare (elem1, elem2) = Q.compare_elem (elem1, elem2)


        (* [5, 6] *)
        (* [2, 5, 3, 6] *)
        (* 
        min = 2
        x = 2
            add min to back of [] = [2]
        min = 3
        x = 5
            add min to front of [2] = [3, 2]
        min = 5
        x = 3
            if min
         *)

        (* 
        - insert all elem into PQue
        - remove min from PQue
        - if min < x
         *)

        fun addElemToPQue [] = emptyPQueue
        |   addElemToPQue xs = 
            let
                val toAddElement = fn (x, accum) => Q.insert (x, accum)
                val resultingPQue = foldl toAddElement Q.empty xs
            in
                resultingPQue
            end

        (* return the list in an increasing order *)
        fun sort [] = emptyList
        |   sort (x::xs) = raise LeftAsExercise
    end