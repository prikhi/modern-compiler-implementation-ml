structure Main : sig
  val main : string -> unit
  val compile : string -> unit
  val test : unit -> unit

  val printAbsyn : string -> unit
  val printIR : string -> unit
  val printAssem : string -> unit

  val runTest : int -> unit
  val printTestAbsyn : int -> unit
  val printTestIR : int -> unit
  val printTestAssem : int -> unit
end = struct

  fun tempString temp =
    case Temp.Table.look (PentiumFrame.tempMap, temp) of
      SOME str =>
        str
    | NONE =>
        Temp.makestring temp

  fun testNumberToName number =
      "../book-code/testcases/test" ^ Int.toString number ^ ".tig"


  fun main filename =
    let
      val syntaxTree = Parse.parse filename
    in
      FindEscape.findEscape syntaxTree;
      Semant.transProg syntaxTree;
      ()
    end


  fun test _ =
      let val testDir = OS.FileSys.openDir "../book-code/testcases/"
          fun getFiles acc = (case OS.FileSys.readDir testDir of
                                      NONE => acc
                                    | SOME x => getFiles (x::acc))
          fun finalName file = "../book-code/testcases/" ^ file
      in app (main o finalName) (getFiles []) end

  val printAbsyn =
    Parse.print

  fun printIR filename =
    let
      val absyn = Parse.parse filename
      val frags = (FindEscape.findEscape absyn; Semant.transProg absyn)
      fun emit (Frame.PROC { body, frame }) =
        let
          val blocks = Canon.traceSchedule (Canon.basicBlocks (Canon.linearize body))
        in
          List.app (fn b => Printtree.printtree (TextIO.stdOut, b)) blocks
        end
        | emit _ =
            ()
    in
      app emit frags
    end

  fun printAssem filename =
    let
      val absyn = Parse.parse filename
      val frags = (FindEscape.findEscape absyn; Semant.transProg absyn)
      fun emit (Frame.PROC { body, frame }) =
        let
          val blocks = Canon.traceSchedule (Canon.basicBlocks (Canon.linearize body))
          val assem = Frame.procEntryExit2 (frame, List.concat (map (PentiumGen.codegen frame) blocks))
          val format0 = Assem.format tempString
          fun assemToString ass =
            let val { prolog, body, epilog } = Frame.procEntryExit3 (frame, ass)
            in  prolog ^ String.concat (List.map format0 body) ^ epilog end
        in
          TextIO.output (TextIO.stdOut, assemToString assem)
        end
        | emit _ =
            ()
    in
      app emit frags
    end

  val runTest =
    main o testNumberToName

  val printTestAbsyn =
    printAbsyn o testNumberToName

  val printTestIR =
    printIR o testNumberToName

  val printTestAssem =
    printAssem o testNumberToName


  (* BOOK CODE - TODO REPLACE THIS *)
  fun emitproc out (Frame.PROC{body,frame}) =
     let val _ = print ("emit " ^ (Symbol.name (Frame.name frame)) ^ "\n")
          val stms = Canon.linearize body
         val stms' = Canon.traceSchedule(Canon.basicBlocks stms)
          val instrs =   List.concat(map (PentiumGen.codegen frame) stms')
         val format0 = Assem.format tempString
      in  app (fn i => TextIO.output(out,format0 i)) instrs
     end
    | emitproc out (Frame.STRING(lab,s)) = ()

   fun withOpenFile fname f =
       let val out = TextIO.openOut fname
        in (f out before TextIO.closeOut out)
        handle e => (TextIO.closeOut out; raise e)
       end

   fun compile filename =
       let val absyn = Parse.parse filename
           val frags = (FindEscape.findEscape absyn; Semant.transProg absyn)
        in
            withOpenFile (filename ^ ".s")
         (fn out => (app (emitproc out) frags))
       end
  (* END BOOK CODE *)
end
