structure PentiumFrame : FRAME = struct

  structure T = Tree

  datatype access
    = InFrame of int
    | InReg of Temp.temp

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

  val FP = Temp.newtemp ()
  val RV = Temp.newtemp ()


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
        T.MEM (T.TEMP reg)

  fun externalCall (name, args) =
    T.CALL ( T.NAME (Temp.namedlabel name), args )

  fun procEntryExit1 (_, body) =
    body
end

structure Frame : FRAME = PentiumFrame
