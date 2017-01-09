structure Main : sig
  val main : string -> unit
  val test : unit -> unit list
end = struct
  fun main filename =
    let
      val syntaxTree = Parse.parse filename
    in
      FindEscape.findEscape syntaxTree;
      Semant.transProg syntaxTree
    end

  fun test _ =
      let val testDir = OS.FileSys.openDir "../book-code/testcases/"
          fun getFiles acc = (case OS.FileSys.readDir testDir of
                                      NONE => acc
                                    | SOME x => getFiles (x::acc))
          fun finalName file = "../book-code/testcases/" ^ file
      in map (main o finalName) (getFiles []) end

end
