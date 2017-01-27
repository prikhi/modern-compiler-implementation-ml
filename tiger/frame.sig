signature FRAME = sig
  type frame
  type access
  type register
  datatype frag
    = PROC of { body : Tree.stm, frame : frame }
    | STRING of Temp.label * string

  val wordSize : int

  val FP : Temp.temp
  val RV : Temp.temp

  val tempMap : register Temp.Table.table

  val specialRegs : Temp.temp list
  val argRegs : Temp.temp list
  val calleeSaves : Temp.temp list
  val callerSaves : Temp.temp list

  val callDests : Temp.temp list
  val divideDests : Temp.temp list
  val dividendRegister : Temp.temp

  val newFrame : { name : Temp.label, formals : bool list } -> frame
  val name : frame -> Temp.label
  val formals : frame -> access list
  val allocLocal : frame -> bool -> access

  val exp : access -> Tree.exp -> Tree.exp

  val externalCall : string * Tree.exp list -> Tree.exp
  val procEntryExit1 : frame * Tree.exp -> Tree.exp
  val procEntryExit2 : frame * Assem.instr list -> Assem.instr list
  val procEntryExit3 : frame * Assem.instr list -> { prolog : string, body : Assem.instr list, epilog : string }

end
