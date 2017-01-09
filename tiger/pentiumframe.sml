structure PentiumFrame : FRAME = struct

  datatype access
    = InFrame of int
    | InReg of Temp.temp

  type frame =
    { formals : access list
    , formalsAllocated : int ref
    , localsAllocated : int ref
    , name : Temp.label
    }


  val name : frame -> Temp.label = #name

  val formals : frame -> access list = #formals


  fun allocFormal (frame : frame) escape =
    if escape then
      let
        val formalNumber = !(#formalsAllocated frame) + 1
        val offset = formalNumber * 8 + 8
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
       InFrame (~ (!(#localsAllocated frame) * 8)))
    else
      InReg (Temp.newtemp ())

end

structure Frame : FRAME = PentiumFrame
