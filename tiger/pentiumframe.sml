structure PentiumFrame : FRAME = struct

  structure T = Tree

  datatype access
    = InFrame of int
    | InReg of Temp.temp

  type register =
    string

  type frame =
    { formals : access list
    , formalsAllocated : int ref
    , localsAllocated : int ref
    , name : Temp.label
    }

  datatype frag
    = PROC of { body : Tree.stm, frame : frame }
    | STRING of Temp.label * string


  val wordSize = 4

  (* Internal Registers *)
  val ESI = Temp.newtemp ()
  val EDI = Temp.newtemp ()

  val ESP = Temp.newtemp ()
  val EBP = Temp.newtemp ()

  val EAX = Temp.newtemp ()
  val EBX = Temp.newtemp ()
  val ECX = Temp.newtemp ()
  val EDX = Temp.newtemp ()

  val FP = EBP
  val RV = EAX

  val tempMap =
    List.foldr
      (fn ((str, reg), table) => Temp.Table.enter (table, reg, str)) Temp.Table.empty
      [ ("ESI", ESI)
      , ("EDI", EDI)
      , ("ESP", ESP)
      , ("EBP", EBP)
      , ("EAX", EAX)
      , ("EBX", EBX)
      , ("ECX", ECX)
      , ("EDX", EDX)
      ]


  val specialRegs = [ EBP, ESP ]
  val argRegs = []
  val calleeSaves = [ EBX, EDI, ESI ]
  val callerSaves = [ EAX, ECX, EDX ]

  val callDests = [ EAX, ECX, EDX, RV ]
  val divideDests = [ EAX, EDX ]
  val dividendRegister = EAX


  val name : frame -> Temp.label = #name
  val formals : frame -> access list = #formals

  fun allocFormal (frame : frame) escape =
    if escape then
      let
        val formalNumber = !(#formalsAllocated frame) + 1
        val offset = formalNumber * wordSize + wordSize
      in
        #formalsAllocated frame := formalNumber;
        InFrame offset
      end
    else
      InReg (Temp.newtemp ())

  fun newFrame { name, formals } =
    let
      val initialFrame =
        { formals = []
        , name = name
        , localsAllocated = ref 0
        , formalsAllocated = ref 0
        }
      val formals' = List.map (allocFormal initialFrame) formals
    in
      { name = name
      , formals = formals'
      , localsAllocated = ref 0
      , formalsAllocated = #formalsAllocated initialFrame
      }
    end

  fun allocLocal (frame : frame) escape =
    if escape then
      (#localsAllocated frame := !(#localsAllocated frame) + 1;
       InFrame (~ (!(#localsAllocated frame) * wordSize)))
    else
      InReg (Temp.newtemp ())


  fun exp access tExp =
    case access of
      InFrame offset =>
        T.MEM (T.BINOP (T.PLUS, tExp, T.CONST offset))
    | InReg reg =>
        T.TEMP reg

  fun externalCall (name, args) =
    T.CALL ( T.NAME (Temp.namedlabel name), args )

  fun procEntryExit1 (_, body) =
    body

  fun procEntryExit2 (_, body) =
    body @ [
      Assem.OPER
        { assem = "", src = [EAX, ESP] @ calleeSaves, dst = [], jump = SOME [] }
    ]

  fun procEntryExit3 (frame : frame, body) =
    { prolog = "PROCEDURE " ^ Symbol.name (#name frame) ^ "\n"
    , body = body
    , epilog = "RET\nEND " ^ Symbol.name (#name frame) ^ "\n"
    }

end

structure Frame : FRAME = PentiumFrame
