
functor PQSortFn(structure Q : PQUEUE) : SORT where type elem = Q.elem =
    struct
        exception LeftAsExercise

        type elem = Q.elem
        type sortedElemList = Q.elem list
        val emptyList = []
        val emptyPQueue = Q.empty
        val PQue = Q.empty
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
                val resultingPQue = foldl toAddElement PQue xs
            in
                resultingPQue
            end

        (* return the list in an increasing order *)
        fun sort [] = emptyList
        | sort (x::xs) = 
            let
                val resultingPQue = addElemToPQue (x::xs)
                val resultingList = if (Q.isEmpty resultingPQue) then
                                        []
                                    else
                                        let
                                            val (minElem, _) =
                                                    Q.deletemin resultingPQue
                                        in
                                            sort xs @ [minElem]
                                            (* case Q.compare_elem (x, minElem)

                                            (* maintain the invarient by
                                            always append the 'x' front of
                                            the list if it's GREATER than
                                            the 'minElem' recieve from the
                                            Priority Queue *)
                                            of  GREATER => x :: sort xs

                                            (* always append 'x' to the back
                                            of the list if it's <= 'minElem'
                                            recieve from the Priority Queue*)
                                            |   _ => sort xs @ [x] *)
                                        end
            in
                resultingList
            end
        
        
        
        
        (* raise LeftAsExercise *)
    end