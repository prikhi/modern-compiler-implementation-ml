structure Main : sig
  val main : string -> unit
  val test : unit -> unit list
  val runTest : int -> unit
  val printTest : int -> unit
end = struct
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
      in map (main o finalName) (getFiles []) end

  fun runTest number =
    main ("../book-code/testcases/test" ^ Int.toString number ^ ".tig")

  fun printTest number =
    Parse.print ("../book-code/testcases/test" ^ Int.toString number ^ ".tig")

end
