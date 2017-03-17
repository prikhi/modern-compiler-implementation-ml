structure RegAlloc : sig
  structure Frame : FRAME
  type allocation = Frame.register Temp.Table.table
  val alloc : Assem.instr list * Frame.frame -> Assem.instr list * allocation
end = struct
  structure GT = Graph.Table
  structure Frame = Frame
  type allocation = Frame.register Temp.Table.table


  fun rewriteProgram instrs spills frame =
    let
      fun rewrite spill (nextInstr, processedInstrs) =
        let
          val result = ref [ nextInstr ]
          fun checkUse _ =
            ()
          fun checkDef _ =
            ()
        in
          ( checkUse ()
          ; checkDef ()
          ; !result @ processedInstrs
          )
        end
      fun rewriteSpill (spill, instrs) =
        List.foldr (rewrite spill) [] instrs
    in
      List.foldr rewriteSpill instrs spills
    end


  fun alloc (instrs, frame) =
    let
      val (graph, nodes) =
        MakeGraph.instrsToGraph instrs
      val (interference, nodeToTemps) =
        Liveness.interferenceGraph graph
      val (resultAllocation, spills) =
        Color.color
          { flow = graph
          , nodeToTemps = nodeToTemps
          , interference = interference
          , initial = Frame.tempMap
          , spillCost = fn _ => 1
          , registers = Frame.registers
          }
    in
      if List.null spills then
        (instrs, resultAllocation)
      else
        alloc (rewriteProgram instrs spills frame, frame)
    end
end
