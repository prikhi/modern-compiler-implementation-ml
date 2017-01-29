structure PentiumGen : CODEGEN = struct
  structure Frame = PentiumFrame
  structure T = Tree
  structure A = Assem


  fun codegen frame stm =
    let
      val instructionList = ref nil
      fun emit instr = instructionList := instr :: !instructionList
      fun result generator = let val t = Temp.newtemp () in generator t; t end

      fun relopToJump oper =
        case oper of
          T.EQ =>
            "JE"
        | T.NE =>
            "JNE"
        | T.LT =>
            "JL"
        | T.LE =>
            "JLE"
        | T.ULT =>
            "JL"
        | T.ULE =>
            "JLE"
        | T.GT =>
            "JG"
        | T.GE =>
            "JGE"
        | T.UGT =>
            "JG"
        | T.UGE =>
            "JGE"

      fun binopToInstr oper =
        case oper of
          T.PLUS =>
            "ADD"
        | T.MINUS =>
            "SUB"
        | T.MUL =>
            "IMUL"
        | T.DIV =>
            "IDIV"
        | T.AND =>
            "AND"
        | T.OR =>
            "OR"
        | T.LSHIFT =>
            "SHL"
        | T.RSHIFT =>
            "SHR"
        | T.XOR =>
            "XOR"
        | T.ARSHIFT =>
            ErrorMsg.impossible "PentiumGen.binopToInstr does not implement ARSHIFT"

      fun plusMinusInt i =
        if i < 0 then
          "-" ^ Int.toString (abs i)
        else
          "+" ^ Int.toString i

      fun fixNegativeInt i =
        if i < 0 then
          "-" ^ Int.toString (abs i)
        else
          Int.toString i

      fun munchStm stm =
        case stm of
          T.SEQ (a, b) =>
            (munchStm a; munchStm b)
        | T.EXP (T.CONST _) =>
            ()
        | T.EXP e =>
            (munchExp e; ())
        | T.LABEL l =>
            emit (A.LABEL { assem = (Symbol.name l ^ ": "), lab = l })
        | T.MOVE (T.TEMP d, T.TEMP s) =>
            emit (A.MOVE
              { assem = "MOV `d0, `s0"
              , src = s, dst = d
              })
        | T.MOVE (T.TEMP d, T.MEM (T.BINOP (T.PLUS, T.TEMP s, T.CONST c))) =>
            emit (A.OPER
              { assem = "MOV `d0, [`s0" ^ plusMinusInt c ^ "]\n"
              , src = [s], dst = [d], jump = NONE
              })
        | T.MOVE (T.TEMP d, T.MEM (T.BINOP (T.PLUS, T.CONST c, T.TEMP s))) =>
            emit (A.OPER
              { assem = "MOV `d0, [`s0" ^ plusMinusInt c ^"]\n"
              , src = [s], dst = [d], jump = NONE
              })
        | T.MOVE (T.TEMP d, T.MEM (T.BINOP (T.PLUS, T.TEMP s0, T.TEMP s1))) =>
            emit (A.OPER
              { assem = "MOV `d0, [`s0+`s1]\n"
              , src = [s0, s1], dst = [d], jump = NONE
              })
        | T.MOVE (T.TEMP d, T.MEM (T.BINOP (T.MINUS, T.TEMP s, T.CONST c))) =>
            emit (A.OPER
              { assem = "MOV `d0, [`s0" ^ plusMinusInt (~1 * c) ^ "]\n"
              , src = [s], dst = [d], jump = NONE
              })
        | T.MOVE (T.MEM (T.TEMP d), e) =>
            emit (A.OPER
              { assem = "MOV DWORD PTR [`d0], `s0\n"
              , src = [munchExp e], dst = [d], jump = NONE
              })
        | T.MOVE (T.MEM (T.BINOP (T.PLUS, T.TEMP d0, T.TEMP d1)), e) =>
            emit (A.OPER
              { assem = "MOV DWORD PTR [`d0+`d1], `s0\n"
              , src = [munchExp e], dst = [d0, d1], jump = NONE
              })
        | T.MOVE (T.MEM (T.BINOP (T.PLUS, T.CONST c1, T.TEMP d)), T.CONST c2) =>
            (* Record Initialization *)
            emit (A.OPER
              { assem = "MOV DWORD PTR [`d0" ^ plusMinusInt c1 ^ "], " ^ fixNegativeInt c2 ^ "\n"
              , src = [], dst = [d], jump = NONE
              })
        | T.MOVE (T.MEM (T.BINOP (T.PLUS, T.CONST c, T.TEMP d)), e) =>
            emit (A.OPER
              { assem = "MOV DWORD PTR [`d0" ^ plusMinusInt c ^ "], `s0\n"
              , src = [munchExp e], dst = [d], jump = NONE
              })
        | T.MOVE (T.MEM (T.BINOP (T.PLUS, T.TEMP d, T.CONST c1)), T.CONST c2) =>
            (* Record Initialization *)
            emit (A.OPER
              { assem = "MOV DWORD PTR [`d0" ^ plusMinusInt c1 ^ "], " ^ fixNegativeInt c2 ^ "\n"
              , src = [], dst = [d], jump = NONE
              })
        | T.MOVE (T.MEM (T.BINOP (T.PLUS, T.TEMP d, T.CONST c)), e) =>
            emit (A.OPER
              { assem = "MOV DWORD PTR [`d0" ^ plusMinusInt c ^ "], `s0\n"
              , src = [munchExp e], dst = [d], jump = NONE
              })
        | T.MOVE (T.MEM (T.BINOP (T.MINUS, T.TEMP d, T.CONST c)), e) =>
            emit (A.OPER
              { assem = "MOV DWORD PTR [`d0" ^ plusMinusInt (~1 * c) ^ "], `s0\n"
              , src = [munchExp e], dst = [d], jump = NONE
              })
        | T.MOVE (T.MEM e1, e2) =>
            emit (A.OPER
              { assem = "MOV [`d0], `s0\n"
              , src = [munchExp e2], dst = [munchExp e1], jump = NONE
              })
        | T.MOVE (T.TEMP t, e2) =>
            emit (A.OPER
              { assem = "MOV `d0, `s0\n"
              , src = [munchExp e2], dst = [t], jump = NONE
              })
        | T.MOVE _ =>
            ErrorMsg.impossible "PentiumGen.munchStm receivied unexpected MOVE operand"
        | T.JUMP (T.NAME jumpPoint, labels) =>
            emit (A.OPER
              { assem = "JMP `j0\n"
              , src = [], dst = [], jump = SOME [ jumpPoint ]
              }
            )
        | T.JUMP (e, labels) =>
            emit (A.OPER
              { assem = "JMP `s0\n"
              , src = [munchExp e], dst = [], jump = SOME labels
              }
            )
        | T.CJUMP (oper, e1, e2, t, f) =>
            emit (A.OPER
              { assem = "CMP `s0, `s1\n" ^ relopToJump oper ^ " `j0\nJMP `j1\n"
              , src = [munchExp e1, munchExp e2]
              , dst = [] , jump = SOME [t, f]
              }
            )

      and munchExp exp : A.temp =
        case exp of
          T.CONST c =>
            result (fn r =>
              emit (A.OPER
                { assem = "MOV `d0, " ^ Int.toString c ^ "\n"
                , src = [], dst = [r], jump = NONE
                })
            )
        | T.TEMP t =>
            t
        | T.ESEQ (stm, exp) =>
            (munchStm stm; munchExp exp)
        | T.BINOP (oper, e1, e2) =>
            if oper = T.DIV then
              result (fn r =>
                (emit (A.MOVE
                  { assem = "MOV `d0, `s0\n"
                  , src = munchExp e1, dst = Frame.dividendRegister
                  }
                 );
                 emit (A.OPER
                  { assem = "IDIV `s0\n"
                  , src = [munchExp e2], dst = Frame.divideDests, jump = NONE
                  }
                 );
                 emit (A.MOVE
                  { assem = "MOV `d0, `s0\n"
                  , src = Frame.dividendRegister, dst = r
                  }
                 )
                )
              )
            else
              result (fn r =>
                (emit (A.MOVE
                    { assem = "MOV `d0, `s0\n"
                    , src = munchExp e1, dst = r
                    }
                 );
                 emit (A.OPER
                    { assem = binopToInstr oper ^ " `d0, `s0\n"
                    , src = [munchExp e2], dst = [r], jump = NONE
                    }
                 )
                )
              )
        | T.CALL (T.NAME label, args) =>
            result (fn r =>
              (emit (A.OPER
                 { assem = "CALL `j0\n"
                 , src = munchArgs (0, args), dst = Frame.callDests
                 , jump = SOME [ label ]
                 }
               );
               emit (A.MOVE
                 { assem = "MOV `d0, `s0\n"
                 , src = Frame.RV, dst = r
                 }
               )
              )
            )
        | T.CALL (exp, args) =>
            result (fn r =>
              (emit (A.OPER
                 { assem = "CALL `s0\n"
                 , src = munchExp exp :: munchArgs (0, args), dst = Frame.callDests
                 , jump = NONE
                 }
               );
               emit (A.MOVE
                 { assem = "MOV `d0, `s0\n"
                 , src = Frame.RV, dst = r
                 }
               )
              )
            )
        | T.MEM (T.BINOP (T.PLUS, e, T.CONST c)) =>
            result (fn r =>
              emit (A.OPER
                { assem = "MOV `d0, [`s0" ^ plusMinusInt c ^ "]\n"
                , src = [munchExp e], dst = [r], jump = NONE
                })
            )
        | T.MEM (T.BINOP (T.PLUS, T.CONST c, e)) =>
            result (fn r =>
              emit (A.OPER
                { assem = "MOV `d0, [`s0" ^ plusMinusInt c ^ "]\n"
                , src = [munchExp e], dst = [r], jump = NONE
                })
            )
        | T.MEM (T.BINOP (T.MINUS, e, T.CONST c)) =>
            result (fn r =>
              emit (A.OPER
                { assem = "MOV `d0, [`s0" ^ plusMinusInt (~1 * c) ^ "]\n"
                , src = [munchExp e], dst = [r], jump = NONE
                })
            )
        | T.MEM (T.CONST c) =>
            result (fn r =>
              emit (A.OPER
                { assem = "MOV `d0, [" ^ Int.toString c ^ "]\n"
                , src = [], dst = [r], jump = NONE
                })
            )
        | T.MEM exp =>
            result (fn r =>
              emit (A.OPER
                { assem = "MOV `d0, [`s0]\n"
                , src = [munchExp exp],  dst = [r], jump = NONE
                }
              )
            )
        | T.NAME label =>
            result (fn r =>
              emit (A.OPER
                { assem = "LEA `d0, [" ^ Symbol.name label ^ "]\n"
                , src = [], dst = [r], jump = SOME [label]
                }
              )
            )
      and munchArgs (i, args) =
        case args of
          [] =>
            []
        | a :: al =>
            munchExp a :: munchArgs (i + 1, al)
    in
      munchStm stm;
      List.rev (!instructionList)
    end
end
