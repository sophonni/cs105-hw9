functor PQSortFn(structure Q : PQUEUE) :> SORT where type elem = Q.elem =
    struct
        exception LeftAsExercise

        type elem = Q.elem
        type sortedElemList = Q.elem list
        val emptyList = []
        val emptyPQueue = Q.empty
        val PQue = Q.empty
        fun compare (elem1, elem2) = Q.compare_elem (elem1, elem2)

        (*  Function: addElemToPQue
         *  Purpose: Given a list of elements, add each element into a
         *          Priority Queue and returns the resulting Priority Queue.
         *
        *)
        fun addElemToPQue [] = emptyPQueue
        |   addElemToPQue xs = 
            let
                val toAddElement = fn (x, accum) => Q.insert (x, accum)
                val resultingPQue = foldl toAddElement PQue xs
            in
                resultingPQue
            end
        
        (*  Function: dequeMinAndCreateSortedList
         *  Purpose: Given a Priority Queue, returns a list of elements
         *          that are in the Priority Queue, in a decending order.
         *
        *)
        fun dequeMinAndCreateSortedList pq =
            if (Q.isEmpty pq) then
                []
            else
                let
                    val (minElem, remaindingQue) = Q.deletemin pq
                in
                    dequeMinAndCreateSortedList remaindingQue @ [minElem]
                end

        (*  Function: sort
         *  Purpose: Given a list of elements, returns a sorted list of
         *          those elements in a decending order.
         *
        *)
        fun sort [] = emptyList
        |   sort (x::xs) = 
            let
                val resultingPQue = addElemToPQue (x::xs)
                val resultingList = dequeMinAndCreateSortedList resultingPQue
            in
                resultingList
            end
    end