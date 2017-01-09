signature TRANSLATE = sig
  type exp
  type level
  type access

  val outermost : level
  val newLevel : { parent : level, name : Temp.label, formals : bool list } -> level
  val formals : level -> access list
  val allocLocal : level -> bool -> access
end

structure Translate : TRANSLATE = struct
  type exp =
    unit

  datatype level =
    Level of
      { parent : level option
      , frame : Frame.frame option
      }

  type access =
    level * Frame.access

  (* The root level of a program *)
  val outermost =
    Level
      { parent = NONE
      , frame = NONE
      }

  (* Add an extra argument to the Frame formals representing the static link *)
  fun newLevel { parent, name, formals } =
    let
      val frame = Frame.newFrame { name = name, formals = true :: formals }
    in
      Level
        { parent = SOME parent
        , frame = SOME frame
        }
    end

  (* Remove the Frame formal that represents the static link *)
  fun formals (Level level) =
    List.tl
      (List.map (fn f => (Level level, f))
        (Option.getOpt (Option.map Frame.formals (#frame level), [])))

  (* Forward local variable allocation to the Frame *)
  fun allocLocal (Level level) escape =
    case #frame level of
      NONE =>
        ErrorMsg.impossible
          "Translator attempted to allocate local variable at outermost level"
    | SOME frame =>
        (Level level, Frame.allocLocal frame escape)

end
