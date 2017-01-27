signature TRANSLATE = sig
  type exp
  type level
  type access
  type breakpoint

  val outermost : level
  val newLevel : { parent : level, name : Temp.label, formals : bool list } -> level
  val formals : level -> access list
  val allocLocal : level -> bool -> access

  val newBreakpoint : unit -> breakpoint

  val simpleVar : access * level -> exp
  val fieldVar : exp * int -> exp
  val subscriptVar : exp * exp -> exp

  val intExp : int -> exp
  val stringExp: string -> exp
  val nilExp : exp
  val assignExp : exp * exp -> exp
  val callExp : Temp.label * level * exp list * level -> exp
  val seqExp : exp list -> exp
  val ifThenExp : exp * exp -> exp
  val ifThenElseExp : exp * exp * exp -> exp
  val whileExp : exp * exp * breakpoint-> exp
  val breakExp : breakpoint -> exp
  val arrayExp : exp * exp -> exp
  val recordExp : exp list -> exp
  val letExp : exp list * exp -> exp

  val intOpExp : exp * exp * Absyn.oper -> exp
  val intCondExp : exp * exp * Absyn.oper -> exp
  val stringCondExp : exp * exp * Absyn.oper -> exp
  val arrayRecordEqualityExp : exp * exp * Absyn.oper -> exp

  val functionDec : Temp.label * level * exp -> unit

  val procEntryExit : { level : level, body : exp } -> unit
  val stringEntry : Temp.label * string -> unit
  val getResult : unit -> Frame.frag list
end

structure Translate : TRANSLATE = struct
  structure T = Tree

  datatype exp
    = Ex of T.exp
    | Nx of T.stm
    | Cx of Temp.label * Temp.label -> T.stm

  datatype level
    = Top
    | Level of
        { parent : level
        , frame : Frame.frame
        , unique : unit ref
        }

  type access =
    level * Frame.access

  datatype breakpoint =
    BreakPoint of Temp.label

  (* The root level of a program *)
  val outermost =
    Top

  (* Add an extra argument to the Frame formals representing the static link *)
  fun newLevel { parent, name, formals } =
    let
      val frame = Frame.newFrame { name = name, formals = true :: formals }
    in
      Level
        { parent = parent
        , frame = frame
        , unique = ref ()
        }
    end

  (* Remove the Frame formal that represents the static link *)
  fun formals (Level level) =
        List.tl
          (List.map (fn f => (Level level, f)) (Frame.formals (#frame level)))
    | formals Top =
        []

  fun staticLinks (Level currentLevel, Level finalLevel) =
        if #unique currentLevel = #unique finalLevel then
          T.TEMP Frame.FP
        else
          (case Frame.formals (#frame currentLevel) of
            [] =>
              ErrorMsg.impossible "Translate.staticLinks could not find static link in formals"
          | sl :: _ =>
              Frame.exp sl (staticLinks (#parent currentLevel, Level finalLevel))
          )
    | staticLinks (Top, _) =
        ErrorMsg.impossible "Translate.staticLinks passed Top level as current"
    | staticLinks (_, Top) =
        ErrorMsg.impossible "Translate.staticLinks passed Top level as final"


  (* Forward local variable allocation to the Frame *)
  fun allocLocal (Level level) escape =
        (Level level, Frame.allocLocal (#frame level) escape)
    | allocLocal Top escape =
        ErrorMsg.impossible "Translate.allocLocal passed Top level"


  fun newBreakpoint _ =
    BreakPoint (Temp.newlabel ())


  fun seq (exps : Tree.stm list) : Tree.stm =
    case exps of
      [] =>
        T.EXP (T.CONST 0)
    | x :: [] =>
        x
    | x :: xs =>
        T.SEQ (x, seq xs)

  fun unEx exp =
    case exp of
      Ex e =>
        e
    | Nx s =>
        T.ESEQ (s, T.CONST 0)
    | Cx c =>
        let
          val r = Temp.newtemp ()
          val t = Temp.newlabel () and f = Temp.newlabel ()
        in
          T.ESEQ
            ( seq
              [ T.MOVE (T.TEMP r, T.CONST 1)
              , c (t, f)
              , T.LABEL f
              , T.MOVE (T.TEMP r, T.CONST 0)
              , T.LABEL t
              ]
            , T.TEMP r
            )
        end

  fun unNx exp =
    case exp of
      Ex e =>
        T.EXP e
    | Nx s =>
        s
    | Cx c =>
        let
          val t = Temp.newlabel () and f = Temp.newlabel ()
        in
          seq
            [ c (t, f)
            , T.LABEL t
            , T.LABEL f
            ]
        end

  fun unCx exp =
    case exp of
      Ex (T.CONST 0) =>
        (fn (t, f) => T.JUMP (T.NAME f, [f]))
    | Ex (T.CONST _) =>
        (fn (t, f) => T.JUMP (T.NAME t, [t]))
    | Ex e =>
        (fn (t, f) => T.CJUMP (T.NE, T.CONST 0, e, t, f))
    | Nx _ =>
        ErrorMsg.impossible "Translate.unCx received an Nx value"
    | Cx c =>
        c


  val results : Frame.frag list ref =
    ref []

  fun procEntryExit { level = Level level, body } =
    results := Frame.PROC { body = T.SEQ (T.LABEL (Frame.name (#frame level)),unNx body), frame = #frame level } :: !results
    | procEntryExit { level = TOP, ... } =
        ErrorMsg.impossible "Translate.procEntryExit passed Top level"

  fun stringEntry frag =
    results := Frame.STRING frag :: !results

  fun getResult _ =
    let
      val temp = !results
    in
      (results := []; temp)
    end


  fun simpleVar ((varLevel, access), currentLevel) =
      Ex (Frame.exp access (staticLinks (currentLevel, varLevel)))

  fun fieldVar (recordExp, fieldNumber) =
    Ex
      ( T.MEM
        ( T.BINOP
          ( T.MINUS
          , unEx recordExp
          , T.CONST (fieldNumber * Frame.wordSize)
          )
        )
      )

  fun subscriptVar (arrayExp, subscriptExp) =
    Ex
      ( T.MEM
        ( T.BINOP
          ( T.MINUS
          , unEx arrayExp
          , T.BINOP
            ( T.MUL
            , T.CONST (Frame.wordSize)
            , unEx subscriptExp
            )
          )
        )
      )


  fun intExp i =
    Ex ( T.CONST i )

  fun stringExp s =
    let
      val label = Temp.newlabel ()
    in
      (stringEntry (label, s); Ex (T.NAME label))
    end

  val nilExp =
    Ex ( T.MEM ( T.CONST 0 ) )

  fun assignExp (varExp, valExp) =
    Nx ( T.MOVE (unEx varExp, unEx valExp) )

  fun callExp (functionLabel, Level functionLevel, argExps, callerLevel) =
        (case #parent functionLevel of
           Level _ =>
             Ex
               ( T.CALL
                 ( T.NAME functionLabel
                 , staticLinks (callerLevel, #parent functionLevel) :: List.map unEx argExps
                 )
               )
         | Top =>
             Ex (Frame.externalCall (Symbol.name functionLabel, List.map unEx argExps))
        )
    | callExp (functionLabel, Top, argExps, callerLevel) =
        ErrorMsg.impossible "Translate.callExp passed function level of Top"

  fun seqExp exps =
    case exps of
      [] =>
        Ex (T.CONST 0)
    | e :: [] =>
        e
    | e :: es =>
        Ex ( T.ESEQ ( unNx e, unEx (seqExp es) ) )

  fun ifThenExp (testExp, thenExp) =
    let
      val t = Temp.newlabel () and f = Temp.newlabel ()
    in
      Ex
        ( T.ESEQ
          ( seq
            [ (unCx testExp)(t, f)
            , T.LABEL t
            , unNx thenExp
            , T.LABEL f
            ]
          , T.CONST 0
          )
        )
    end

  fun ifThenElseExp (testExp, thenExp, elseExp) =
    let
      val t = Temp.newlabel () and f = Temp.newlabel() and join = Temp.newlabel ()
      val r = Temp.newtemp ()
    in
      Ex
        ( T.ESEQ
          ( seq
            [ (unCx testExp)(t, f)
            , T.LABEL t
            , T.MOVE ( T.TEMP r, unEx thenExp )
            , T.JUMP ( T.NAME join, [join] )
            , T.LABEL f
            , T.MOVE ( T.TEMP r, unEx elseExp )
            , T.LABEL join
            ]
          , T.TEMP r
          )
        )
    end

  fun whileExp (testExp, bodyExp, BreakPoint doneLabel) =
    let
      val testLabel = Temp.newlabel () and bodyLabel = Temp.newlabel ()
    in
      Nx
        ( seq
          [ T.LABEL testLabel
          , (unCx testExp)(bodyLabel, doneLabel)
          , T.LABEL bodyLabel
          , unNx bodyExp
          , T.JUMP (T.NAME testLabel, [testLabel])
          , T.LABEL doneLabel
          ]
        )
    end

  fun breakExp (BreakPoint doneLabel) =
    Ex ( T.ESEQ ( T.JUMP (T.NAME doneLabel, [doneLabel]), T.CONST 0 ) )

  fun arrayExp (sizeExp, initExp) =
    let
      val r = Temp.newtemp ()
    in
      Ex
        ( T.ESEQ
          ( T.MOVE
            ( T.TEMP r
            , Frame.externalCall ("initArray", [ unEx sizeExp, unEx initExp ])
            )
          , T.TEMP r
          )
        )
    end

  fun recordExp fieldExps =
    let
      val r = Temp.newtemp ()
      fun indexedmap f items =
        let
          fun run (acc, l) =
            case l of
              [] =>
                []
            | x :: xs =>
                f (acc, x) :: run (acc + 1, xs)
        in
          run (0, items)
        end
      val fieldTrees =
        seq
          ( indexedmap
            ( fn (i, x) =>
              T.MOVE
                ( T.MEM
                  (T.BINOP (T.PLUS, T.CONST (i * Frame.wordSize), T.TEMP r))
                , unEx x
                )
            ) fieldExps
          )
    in
      Ex
        ( T.ESEQ
          ( seq
            [ T.MOVE
                ( T.TEMP r
                , Frame.externalCall
                    ("allocRecord", [ T.CONST (List.length fieldExps * Frame.wordSize) ])
                )
              , fieldTrees
            ]
          , T.TEMP r
          )
        )
    end

  fun letExp (assignExps, bodyExp) =
    Ex (T.ESEQ (seq (List.map unNx assignExps), unEx bodyExp))



  fun intOpExp (exp1, exp2, oper) =
    let
      val oper' =
        case oper of
          Absyn.PlusOp =>
            T.PLUS
        | Absyn.MinusOp =>
            T.MINUS
        | Absyn.TimesOp =>
            T.MUL
        | Absyn.DivideOp =>
            T.DIV
        | _ =>
            ErrorMsg.impossible "Translate.intOpExp passed non-int only operator"
    in
      Ex
        ( T.BINOP
          ( oper'
          , unEx exp1
          , unEx exp2
          )
        )
    end

  fun intCondExp (exp1, exp2, oper) =
    let
      val oper' =
        case oper of
          Absyn.EqOp =>
            T.EQ
        | Absyn.NeqOp =>
            T.NE
        | Absyn.LtOp =>
            T.LT
        | Absyn.LeOp =>
            T.LE
        | Absyn.GtOp =>
            T.GT
        | Absyn.GeOp =>
            T.GE
        | _ =>
            ErrorMsg.impossible "Translate.intCondExp passed non-conditional operator"
    in
      Cx (fn (t, f) => T.CJUMP ( oper', unEx exp1, unEx exp2, t, f ))
    end

  fun stringCondExp (exp1, exp2, oper) =
    let
      val t = Temp.newlabel () and f = Temp.newlabel() and r = Temp.newlabel ()
      fun wrapper0 (expr, cmp) =
        Cx (fn (t, f) => T.CJUMP (cmp, T.CONST 0, unEx expr, t, f))
      fun wrapper1 (expr, cmp) =
        Cx (fn (t, f) => T.CJUMP (cmp, T.CONST 1, unEx expr, t, f))
    in
      case oper of
        Absyn.EqOp =>
          wrapper1
            ( Ex (Frame.externalCall ("stringEqual", [ unEx exp1, unEx exp2 ]))
            , T.EQ
            )
      | Absyn.NeqOp =>
          wrapper1
            ( Ex (Frame.externalCall ("stringEqual", [ unEx exp1, unEx exp2 ]))
            , T.NE
            )
      | Absyn.LtOp =>
          wrapper0
            ( Ex (Frame.externalCall ("stringCompare", [ unEx exp1, unEx exp2 ]))
            , T.LT
            )
      | Absyn.LeOp =>
          wrapper0
            ( Ex (Frame.externalCall ("stringCompare", [ unEx exp1, unEx exp2 ]))
            , T.LE
            )
      | Absyn.GtOp =>
          wrapper0
            ( Ex (Frame.externalCall ("stringCompare", [ unEx exp1, unEx exp2 ]))
            , T.GT
            )
      | Absyn.GeOp =>
          wrapper0
            ( Ex (Frame.externalCall ("stringCompare", [ unEx exp1, unEx exp2 ]))
            , T.GE
            )
      | _ =>
          ErrorMsg.impossible "Translate.stringCondExp passed non-conditional operator"
    end

  fun arrayRecordEqualityExp (exp1, exp2, oper) =
    case oper of
      Absyn.EqOp =>
        Cx (fn (t, f) => T.CJUMP (T.EQ, unEx exp1, unEx exp2, t, f))
    | Absyn.NeqOp =>
        Cx (fn (t, f) => T.CJUMP (T.NE, unEx exp1, unEx exp2, t, f))
    | _ =>
        ErrorMsg.impossible "Translate.arrayRecordEqualityExp passed non-equality operator"


  fun functionDec (label, Level level, bodyExp) =
        let
          val body =
            Nx
              ( T.MOVE
                ( T.TEMP Frame.RV
                , Frame.procEntryExit1 (#frame level, unEx bodyExp)
                )
              )
        in
          procEntryExit { level = Level level, body = body  }
        end
    | functionDec (_, Top, _) =
        ErrorMsg.impossible "Translate.functionDec passed Top level"

end
