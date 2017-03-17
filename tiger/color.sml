structure Color : sig

  structure Frame : FRAME
  type allocation = Frame.register Temp.Table.table

  val color : { flow : Flow.flowgraph
              , nodeToTemps : Flow.Graph.node -> Temp.temp list
              , interference : Liveness.igraph
              , initial : allocation
              , spillCost : Graph.node -> int
              , registers : Frame.register list
              } -> allocation * Temp.temp list


end = struct

  structure Frame = Frame
  structure GT = Graph.Table

  type allocation = Frame.register Temp.Table.table

  fun color { flow = Flow.FGRAPH flow , nodeToTemps, interference, initial = allocation, spillCost, registers } =
    let
      val (Liveness.IGRAPH { graph, moves, tNode, gTemp }) = interference
      val nodes = Graph.nodes graph
      val k = List.length registers

      (* Work Lists *)
      val precolored = ref []
      val initial = ref []
      val simplifyWorklist = ref []
      val freezeWorklist = ref []
      val spillWorklist = ref []
      val spilledNodes = ref []
      val coalescedNodes = ref []
      val coloredNodes = ref []
      val selectStack = ref []

      (* Move Sets *)
      val coalescedMoves = ref []
      val constrainedMoves = ref []
      val frozenMoves = ref []
      val worklistMoves = ref moves
      val activeMoves = ref []

      val adjSet = ref []
      val adjList = ref GT.empty
      val degree = ref GT.empty
      val moveList = ref GT.empty
      val alias = ref GT.empty
      val color = ref GT.empty

      (** Utility Functions **)
      (* Test whether an edge is in the adjacency set *)
      fun adjSetMember edge =
        ListUtils.isMemberBy Graph.edgeEq edge (!adjSet)
      (* Test whether a node is precolored *)
      fun isPrecolored node =
        Option.isSome (Temp.Table.look (allocation, gTemp node))
      (* Add a node to a node's adjacency list *)
      fun updateAdjList listNode newNode =
        case GT.look (!adjList, listNode) of
          NONE =>
            adjList := GT.enter (!adjList, listNode, [newNode])
        | SOME nodeList =>
            adjList := GT.enter (!adjList, listNode, newNode :: nodeList)
      (* Increase the degree of a node by 1 *)
      fun incrementDegree node =
        case GT.look (!degree, node) of
          NONE =>
            degree := GT.enter (!degree, node, 1)
        | SOME d =>
            degree := GT.enter (!degree, node, d + 1)
      fun updateTableList (t, k, v) =
        case GT.look (!t, k) of
          NONE =>
            t := GT.enter (!t, k, [v])
        | SOME l =>
            t := GT.enter (!t, k, v :: l)


      (* Set inital nodes *)
      val _ =
        ( initial := (List.filter (not o isPrecolored) nodes)
        ; precolored := List.filter isPrecolored nodes
        )


      (** Build **)
      (* Add an Edge to the Adjacency Set & List *)
      fun addEdge node1 node2 =
        if not (adjSetMember (node1, node2)) andalso not (Graph.eq (node1, node2)) then
          ( adjSet := (node1, node2) :: (node2, node1) :: !adjSet
          ; if not (isPrecolored node1) then
              ( updateAdjList node1 node2
              ; incrementDegree node1
              )
            else
              ()
          ; if not (isPrecolored node2) then
              ( updateAdjList node2 node1
              ; incrementDegree node2
              )
            else
              ()
          )
        else
          ()

      (* Build the initial coloring graph *)
      fun build _ =
        let
          fun run node =
            let
              val live =
                ref (nodeToTemps node)
              val instrs =
                Graph.nodes (#control flow)
              fun isMove n =
                case GT.look (#isMove flow, n) of
                  NONE =>
                    false
                | SOME b =>
                    b
              fun getMove instr =
                ( tNode (List.hd (GraphUtils.getListValue (#def flow, instr)))
                , tNode (List.hd (GraphUtils.getListValue (#use flow, instr)))
                )
              fun enqueue instr =
                ( if isMove instr then
                    ( live := ListUtils.difference (!live) (GraphUtils.getListValue (#use flow, instr))
                    ; List.app (fn i => updateTableList (moveList, tNode i, getMove instr))
                        (GraphUtils.getListValue (#use flow, instr) @ GraphUtils.getListValue (#def flow, instr))
                    ; worklistMoves := (getMove instr) :: (!worklistMoves)
                    )
                  else
                    ()
                ; live := (GraphUtils.getListValue (#def flow, instr)) @ !live
                ; List.map (fn d => List.map (fn l => addEdge l d) (List.map tNode (!live)))
                    (List.map tNode (GraphUtils.getListValue (#def flow, instr)))
                ; live := (GraphUtils.getListValue (#use flow, instr)) @ (ListUtils.difference (!live) (GraphUtils.getListValue (#def flow, instr)))
                )
            in
              List.app enqueue instrs
            end
        in
          List.app run (List.rev nodes)
        end


      (** Make Worklist **)
      (* Get the active & worklist moves for a node *)
      fun nodeMoves n =
        ListUtils.intersectionBy Graph.edgeEq (GraphUtils.getListValue (!moveList, n))
          (!activeMoves @ !worklistMoves)

      (* Determine if a node is move related *)
      fun moveRelated node =
        not (List.null (nodeMoves node))

      (* Fill the spill, freeze, & simplify worklists *)
      fun makeWorklist _ =
        let
          fun make (n : Graph.node) : unit =
            if GraphUtils.getValue (!degree, n, k) >= k then
              spillWorklist := n :: (!spillWorklist)
            else if moveRelated(n) then
              freezeWorklist := n :: (!freezeWorklist)
            else
              simplifyWorklist := n :: (!simplifyWorklist)
        in
          List.app make (!initial)
        end


      (** Simplify **)
      (* Find the adjacent nodes *)
      fun adjacent node =
        ListUtils.differenceBy Graph.eq (GraphUtils.getListValue (!adjList, node))
          (!selectStack @ !coalescedNodes)

      (* Move an active moves in the nodes/moves to the worklist *)
      fun enableMoves nodes =
        let
          fun enable move =
            if ListUtils.isMemberBy Graph.edgeEq move (!activeMoves) then
              ( activeMoves := ListUtils.differenceBy Graph.edgeEq (!activeMoves) [move]
              ; worklistMoves := move :: (!worklistMoves)
              )
            else
              ()
        in
          List.map (fn n => List.map enable (nodeMoves n)) nodes
        end

      (* Reduce the degree of a node by 1, enabling moves if applicable *)
      fun decrementDegree node =
        let
          val d =
            GraphUtils.getValue (!degree, node, k + 1)
        in
          ( degree := GT.enter (!degree, node, d - 1)
          ; if d = k then
              ( enableMoves (node :: (adjacent node))
              ; spillWorklist := ListUtils.differenceBy Graph.eq (!spillWorklist) [node]
              ; if moveRelated node then
                  freezeWorklist := node :: (!freezeWorklist)
                else
                  simplifyWorklist := node :: (!simplifyWorklist)
              )
            else
              ()
          )
        end

      (* Simplify the graph using the simplifyWorklist *)
      fun simplify _ =
        let
          val (n :: simplifyWorklist') =
            !simplifyWorklist
        in
          ( simplifyWorklist := simplifyWorklist'
          ; selectStack := n :: !selectStack
          ; List.app decrementDegree (adjacent n)
          )
        end


      (** Coalesce **)
      (* Add the node to the simplify worklist *)
      fun addWorkList node =
        let
          val d =
            GraphUtils.getValue (!degree, node, k)
        in
          if (not (isPrecolored node)) andalso (not (moveRelated node)) andalso d < k then
            ( freezeWorklist := ListUtils.intersectionBy Graph.eq (!freezeWorklist) [node]
            ; simplifyWorklist := node :: (!simplifyWorklist)
            )
          else
            ()
        end

      (* Determine whether a move is OK to coalesce *)
      fun ok  (t, r) =
        let
          val d =
            GraphUtils.getValue (!degree, t, k)
        in
          d < k orelse isPrecolored t orelse adjSetMember (t, r)
        end

      (* Determine whether the number of high-degree nodes is less than the register count *)
      fun conservative nodes =
        let
          val count = ref 0
          fun incrementCount node =
            if GraphUtils.getValue (!degree, node, k) >= k then
              count := !count + 1
            else
              ()
        in
          ( List.app incrementCount nodes
          ; !count < k
          )
        end

      (* Follow any aliases to an actual node *)
      fun getAlias node =
        if ListUtils.isMemberBy Graph.eq node (!coalescedNodes) then
          getAlias (GraphUtils.getValue (!alias, node, node))
        else
          node

      (* Combine two nodes *)
      fun combine node1 node2 =
        ( if ListUtils.isMemberBy Graph.eq node2 (!freezeWorklist) then
            freezeWorklist := ListUtils.differenceBy Graph.eq (!freezeWorklist) [node2]
          else
            spillWorklist := ListUtils.differenceBy Graph.eq (!spillWorklist) [node2]
        ; coalescedNodes := node2 :: (!coalescedNodes)
        ; alias := GT.enter (!alias, node2, node1)
        ; moveList :=
          GT.enter
            ( !moveList
            , node1
            , (GraphUtils.getListValue (!moveList, node1)) @
              (GraphUtils.getListValue (!moveList, node2))
            )
        ; enableMoves [node2]
        ; List.app (fn t => (addEdge t node1; decrementDegree t)) (adjacent node2)
        ; if GraphUtils.getValue (!degree, node1, k + 1) >= k andalso ListUtils.isMemberBy Graph.eq node1 (!freezeWorklist) then
            ( freezeWorklist := ListUtils.differenceBy Graph.eq (!freezeWorklist) [node1]
            ; spillWorklist := node1 :: (!spillWorklist)
            )
          else
            ()
        )

      (* Coalesce available moves *)
      fun coalesce _ =
        let
          val ((m as (x', y')) :: worklistMoves') =
            !worklistMoves
          val (x, y) =
            (getAlias x', getAlias y')
          val (u, v) =
            if isPrecolored y then
              (y, x)
            else
              (x, y)
        in
          ( worklistMoves := ListUtils.differenceBy Graph.edgeEq (!worklistMoves) [m]
          ; if Graph.eq (u, v) then
              ( coalescedMoves := m :: !coalescedMoves
              ; addWorkList u
              )
            else if isPrecolored v orelse adjSetMember (u, v) then
              ( constrainedMoves := m :: !constrainedMoves
              ; addWorkList u
              ; addWorkList v
              )
            else if (isPrecolored u andalso List.all (fn t => ok (t, u)) (adjacent v)) orelse
                    ((not (isPrecolored u)) andalso conservative (adjacent u @ adjacent v)) then
              ( coalescedMoves := m :: !coalescedMoves
              ; combine u v
              ; addWorkList u
              )
            else
              activeMoves := m :: !activeMoves
          )
        end

      (** Freeze **)
      (* Freeze any moves related to a node *)
      fun freezeMoves node =
        let
          fun freezeMove move =
            let
              val (x, y) = move
              val v =
                if Graph.eq (getAlias x, getAlias y) then
                  getAlias x
                else
                  getAlias y
              val d =
                GraphUtils.getValue (!degree, v, k)
            in
              ( activeMoves := ListUtils.differenceBy Graph.edgeEq (!activeMoves) [move]
              ; frozenMoves := move :: !frozenMoves
              ; if List.null (nodeMoves v) andalso d < k then
                  ( freezeWorklist := ListUtils.differenceBy Graph.eq (!freezeWorklist) [v]
                  ; simplifyWorklist := v :: !simplifyWorklist
                  )
                else
                  ()
              )
            end
        in
          List.app freezeMove (nodeMoves node)
        end

      (* Freeze a node from the worklist *)
      fun freeze _ =
        let
          val (u :: freezeWorklist') =
            !freezeWorklist
        in
          ( freezeWorklist := ListUtils.differenceBy Graph.eq (!freezeWorklist) [u]
          ; simplifyWorklist := u :: !simplifyWorklist
          ; freezeMoves u
          )
        end


      (** Select Spill **)
      (* Simplify & freeze the spill with the highest cost *)
      fun selectSpill _ =
        let
          val (s :: sW) =
            !spillWorklist
          val m =
            List.foldr (fn (i, max) => if spillCost i > spillCost max then i else max)
              s sW
        in
          ( spillWorklist := ListUtils.differenceBy Graph.eq (!spillWorklist) [m]
          ; simplifyWorklist := m :: !simplifyWorklist
          ; freezeMoves m
          )
        end


      (** Assign Colors **)
      (* Assign a color to each selected node *)
      fun assignColors _ =
        let
          fun popStack _ =
            let
              val (n :: stack') =
                !selectStack
              val okColors =
                ref (List.tabulate (k, fn x => x))
              fun removeAdjacent node =
                if ListUtils.isMemberBy Graph.eq (getAlias node) (!coloredNodes @ !precolored) then
                  okColors := ListUtils.difference (!okColors) [(GraphUtils.getValue (!color, getAlias node, 0))]
                else
                  ()
            in
              ( selectStack := stack'
              ; List.app removeAdjacent (GraphUtils.getListValue (!adjList, n))
              ; if List.null (!okColors) then
                  spilledNodes := n :: !spilledNodes
                else
                  ( coloredNodes := n :: !coloredNodes
                  ; color := GT.enter (!color, n, List.hd (!okColors))
                  )
              )
            end
          fun colorCoalesced node =
            color := GT.enter (!color, node, GraphUtils.getValue (!color, getAlias node, 0))
        in
          ( while not (List.null (!selectStack)) do
              popStack ()
          ; List.app colorCoalesced (!coalescedNodes)
          )
        end



      (** Main **)
      (* Check whether we're done processing the nodes *)
      fun isFinished _ =
        List.all List.null
          [!simplifyWorklist, !freezeWorklist, !spillWorklist]
        andalso List.null (!worklistMoves)

      (* Run the graph coloring algorithm *)
      fun main _ : allocation * Temp.temp list =
        ( build ()
        ; makeWorklist ()
        ; while not (isFinished ()) do
            if not (List.null (!simplifyWorklist)) then
              simplify ()
            else if not (List.null (!worklistMoves)) then
              coalesce ()
            else if not (List.null (!freezeWorklist)) then
              freeze ()
            else
              selectSpill ()
        ; assignColors ()
        ; ( List.foldr
              (fn (n, t) =>
                Temp.Table.enter (t, gTemp n, List.nth (registers, GraphUtils.getValue (!color, n, 0))))
              allocation (!coloredNodes @ !coalescedNodes)
          , List.map gTemp (!spilledNodes))
        )
    in
      main ()
    end

end
