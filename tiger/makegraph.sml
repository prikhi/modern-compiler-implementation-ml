structure MakeGraph : sig
  val instrsToGraph : Assem.instr list -> Flow.flowgraph * Flow.Graph.node list
end = struct
  fun instrsToGraph instrs =
    let
      val initial = 
        Flow.FGRAPH 
          { control = Graph.newGraph ()
          , def = Graph.Table.empty
          , use = Graph.Table.empty
          , isMove = Graph.Table.empty 
          }

      val nodes = List.map (fn _ => Flow.Graph.newNode )

      (* (label, labelNode) list ref *)
      val labelToNode = ref []
      (* (toLabel, fromNode) list ref *)
      val delayedLabelEdges = ref []

      fun mapEdge from = 
        Option.map (fn to => Flow.Graph.mk_edge { from = from, to = to })

      fun addOrDelayLabelEdge from toLabel =
        case List.find (fn (label, _) => label = toLabel) (!labelToNode) of
          NONE =>
            delayedLabelEdges := (toLabel, from) :: !delayedLabelEdges
        | SOME (_, labelNode) =>
            Flow.Graph.mk_edge { from = from, to = labelNode }

      fun reducer (instr, (fallThrough, Flow.FGRAPH { control, def, use, isMove })) =
        let 
          val node =
            Flow.Graph.newNode control
        in
          case instr of
            Assem.MOVE { assem, dst, src } =>
              ( mapEdge node fallThrough
              ; ( SOME node
                , Flow.FGRAPH 
                  { control = control
                  , def = Graph.Table.enter (def, node, [dst])
                  , use = Graph.Table.enter (use, node, [src])
                  , isMove = Graph.Table.enter (isMove, node, true)
                  }
                )
              )
          | Assem.LABEL { assem, lab } =>
              ( mapEdge node fallThrough
              ; labelToNode := (lab, node) :: !labelToNode
              ; ( SOME node
                , Flow.FGRAPH
                  { control = control
                  , def = Graph.Table.enter (def, node, [])
                  , use = Graph.Table.enter (use, node, [])
                  , isMove = Graph.Table.enter (isMove, node, false)
                  }
                )
              )
          | Assem.OPER { assem, dst, src, jump } =>
            ( ( case jump of
                  NONE =>
                    (mapEdge node fallThrough; ())
                | SOME jumpList =>
                    List.app (fn toLabel => addOrDelayLabelEdge node toLabel) jumpList
              )
            ; ( SOME node
              , Flow.FGRAPH
                { control = control
                , def = Graph.Table.enter (def, node, dst)
                , use = Graph.Table.enter (use, node, src)
                , isMove = Graph.Table.enter (isMove, node, false)
                }
              )
            )
        end

      val (_, result as Flow.FGRAPH { control, ... }) =
        List.foldr reducer (NONE, initial) instrs

      fun addMissingLabelEdges _ =
        let
          fun addEdge (toLabel, fromNode) = 
            case List.find (fn (label, _) => toLabel = label) (!labelToNode) of
              NONE =>
                ()
            | SOME (_, labelNode) =>
                Flow.Graph.mk_edge { from = fromNode, to = labelNode }
        in
          List.map addEdge (!delayedLabelEdges); delayedLabelEdges := []
        end
    in
      addMissingLabelEdges ();
      (result, Flow.Graph.nodes control)
    end
end
