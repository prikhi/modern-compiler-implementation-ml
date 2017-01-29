structure Liveness : sig
  datatype igraph
    = IGRAPH of
      { graph : Graph.graph
      , tNode : Temp.temp -> Graph.node
      , gTemp : Graph.node -> Temp.temp
      , moves : (Graph.node * Graph.node) list
      }
  val interferenceGraph : Flow.flowgraph -> igraph * (Flow.Graph.node -> Temp.temp list)
  val show : TextIO.outstream * igraph -> unit
end = struct

  structure FT = Flow.Graph.Table
  val impossible = ErrorMsg.impossible

  datatype igraph
    = IGRAPH of
      { graph : Graph.graph
      , tNode : Temp.temp -> Graph.node
      , gTemp : Graph.node -> Temp.temp
      , moves : (Graph.node * Graph.node) list
      }


  (* Utils *)
  fun unique l : Temp.temp list =
    case l of
      [] =>
        []
    | x :: xs =>
        x :: unique (List.filter (fn y => x <> y) xs)

  val enterUnits =
    List.foldr (fn (k, t') => Temp.Table.enter (t', k, ()))

  fun forceLook r =
    case r of
      SOME s =>
        s
    | NONE =>
        impossible "Liveness found NONE when SOME _ assumed."


  (* Live Sets/Maps *)
  type liveSet = unit Temp.Table.table * Temp.temp list
  type liveMap = liveSet FT.table

  fun initialMaps nodes =
    List.foldr
      (fn (node, { inMap, outMap }) =>
        { inMap = FT.enter (inMap, node, (Temp.Table.empty, []))
        , outMap = FT.enter (outMap, node, (Temp.Table.empty, []))
        }
      )
      { inMap = FT.empty, outMap = FT.empty } nodes

  fun liveMapsEqual map1 map2 =
    ListPair.all (fn ((_, (_, a) : liveSet), (_, (_, b) : liveSet)) => a = b)
      (FT.entries map1, FT.entries map2)




  (* Interference Graph Generation via Live-Out *)
  fun interferenceGraph (Flow.FGRAPH { control, def, use, isMove }) =
    let

      (* Store move nodes *)
      val moves =
        ref []



      (* Update the In & Out LiveMaps for a single iteration of a Node *)
      fun updateInMap node inMap outMap =
        let
          val (liveTable, liveList) =
            forceLook (FT.look (inMap, node))
          val (_, outList) =
            forceLook (FT.look (outMap, node))
          val fromUsed =
            forceLook (Graph.Table.look (use, node))
          val fromDef =
            forceLook (Graph.Table.look (def, node))
          val filteredOut =
            List.filter
              (fn t => not (Option.isSome (List.find (fn d => t = d) fromDef)))
              outList
          val result =
            unique (fromUsed @ filteredOut @ liveList)
        in
          FT.enter
            ( inMap
            , node
            , ( enterUnits liveTable result
              , result )
            )
        end

      fun updateOutMap node inMap outMap =
        let
          val (liveTable, liveList) =
            forceLook (FT.look (outMap, node))
          val result : Temp.temp list =
            unique
              ( List.foldr
                ( fn (s, tempList) =>
                  #2 (forceLook (FT.look (inMap, s)) : liveSet) @ tempList
                )
                liveList (Graph.succ node)
              )
        in
          FT.enter
            ( outMap
            , node
            , ( enterUnits liveTable result
              , result
              )
            )
        end


      (* Loop through the Flow Graph until In/Out LiveMap content stabilizes *)
      fun buildMaps flowNodes (initial as { inMap, outMap }) =
        let
          fun run (node, { inMap', outMap' }) =
            { inMap' = updateInMap node inMap' outMap'
            , outMap' = updateOutMap node inMap' outMap'
            }
          val { inMap', outMap' } =
            List.foldr run { inMap' = inMap, outMap' = outMap } flowNodes
        in
          if (liveMapsEqual inMap inMap' andalso liveMapsEqual outMap outMap') then
            initial
          else
            buildMaps flowNodes { inMap = inMap', outMap = outMap' }
        end

      val { inMap, outMap } =
        buildMaps (Graph.nodes control) { inMap = FT.empty, outMap = FT.empty }


      (* Create & Track Node<->Temp Relationship in Interference Graph *)
      val graph =
        Graph.newGraph ()

      val nodeToTemp : (Graph.node * Temp.temp) list ref =
        ref []

      fun getNodeFromTemp temp =
        case List.find (fn (_, temp') => temp = temp') (!nodeToTemp) of
          NONE =>
            let
              val node =
                Graph.newNode graph
            in
              ( nodeToTemp := (node, temp) :: !nodeToTemp
              ; node
              )
            end
        | SOME (node, _) =>
            node

      fun getTempFromNode node =
        case List.find (fn (node', _) => Graph.eq(node, node')) (!nodeToTemp) of
          NONE =>
            impossible "Liveness.getTempFromNode could not find node."
        | SOME (_, temp) =>
            temp


      (* Build the Interfence Graph *)
      fun buildGraph flowNodes =
        let
          fun addEdges node =
            let
              val fromDef =
                forceLook (Graph.Table.look (def, node))
              val (_, fromOut) =
                forceLook (FT.look (outMap, node))
            in
              List.map
                ( fn d =>
                  List.map
                  ( fn out =>
                    Graph.mk_edge
                      { from = getNodeFromTemp d
                      , to = getNodeFromTemp out
                      }
                  )
                  fromOut
                )
                fromDef
            end
        in
          List.map addEdges flowNodes
        end

    in
      ( buildGraph (Graph.nodes control)
      ; ( IGRAPH
          { graph = graph
          , tNode = getNodeFromTemp
          , gTemp = getTempFromNode
          , moves = !moves
          }
        , fn node => #2 (forceLook (FT.look (outMap, node)))
        )
      )
    end

  fun show _ = ()
end
