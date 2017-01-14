structure Semant : sig
  type venv
  type tenv
  type expty

  val transProg : Absyn.exp -> Frame.frag list
  val transExp : venv * tenv * Translate.level * Translate.breakpoint option -> Absyn.exp -> expty
  val transDec : venv * tenv * Translate.level * Translate.breakpoint option -> Absyn.dec -> {venv: venv, tenv: tenv, exps: Translate.exp list}
  val transTy : tenv * { name : Absyn.symbol, ty : Absyn.ty, pos : Absyn.pos } -> Types.ty
  val transFun : venv * tenv * { formals: Env.ty list, label: Temp.label, level: Translate.level, result: Env.ty } * Translate.breakpoint option * Absyn.fundec -> unit
end = struct
  (* Aliases *)
  structure A = Absyn
  structure T = Types
  structure Tr = Translate
  val error = ErrorMsg.error

  (* Type Definitions *)
  type venv = Env.enventry Symbol.table
  type tenv = T.ty Symbol.table
  type expty = { exp: Translate.exp, ty: T.ty }

  (* Break Checking *)
  val loopNesting = ref 0


  (* Type Checkers *)
  (* Ensure the result is an integer *)
  fun checkInt ({ exp, ty }, pos) =
    if ty = T.INT then
      ()
    else
      (error pos "expected an integer")

  (* Ensure the resut is a string *)
  fun checkString ({ exp, ty }, pos) =
    if ty = T.STRING then
      ()
    else
      (error pos "expected a string")

  (* Ensure the results are both integers *)
  fun checkBothInt (result1, result2, pos) =
    (checkInt (result1, pos); checkInt (result2, pos))

  (* Ensure the results are either both an integer or both a string *)
  fun checkBothIntOrString (result1, result2, pos) =
    case (result1, result2) of
      ({ exp, ty = T.INT }, { exp = _, ty = T.INT }) =>
        ()
    | ({ exp, ty = T.INT }, _) =>
        (error pos "expected an integer")
    | ({ exp, ty = T.STRING }, { exp = _, ty = T.STRING }) =>
        ()
    | ({ exp, ty = T.STRING }, _) =>
        (error pos "expected a string")
    | _ =>
        (error pos "expecting an integer or string")

  (* Ensure both results can be compared by equality *)
  fun checkBothEq (result1, result2, pos) =
    case (result1, result2) of
      ({ exp, ty = T.INT }, _) =>
        checkBothIntOrString (result1, result2, pos)
    | ({ exp, ty = T.STRING }, _) =>
        checkBothIntOrString (result1, result2, pos)
    | ({ exp, ty = T.RECORD (fields1, _) }, { exp = _, ty = T.RECORD (fields2, _) }) =>
        if fields1 = fields2 then
          ()
        else
          (error pos "records are not of the same type")
    | ({ exp, ty = T.RECORD _ }, { exp = _, ty = T.NIL }) =>
        ()
    | ({ exp, ty = T.NIL }, { exp = _, ty = T.RECORD _ }) =>
        ()
    | ({ exp, ty = T.RECORD _ }, _) =>
        (error pos "expecting a record")
    | ({ exp, ty = T.ARRAY (ty1, _) }, { exp = _, ty = T.ARRAY (ty2, _) }) =>
        if ty1 = ty2 then
          ()
        else
          (error pos "type of array's elements mismatched")
    | ({ exp, ty = T.ARRAY _ }, { exp = _, ty }) =>
        (error pos "expecting an array")
    | _ =>
        (error pos "expecting an integer, string, array, or record")

  (* Ensure the results have the same type *)
  fun checkSame (result1, result2, pos) =
    case (result1, result2) of
      ({ exp = _, ty = T.NIL }, { exp = _, ty = T.NIL }) =>
        ()
    | ({ exp = _, ty = T.NIL }, _) =>
        (error pos "expecting nil")
    | ({ exp = _, ty = T.UNIT }, { exp = _, ty = T.UNIT }) =>
        ()
    | ({ exp = _, ty = T.UNIT }, _) =>
        (error pos "expecting unit")
    | ({ exp = _, ty = T.NAME _ }, _) =>
        ()
    | _ =>
        checkBothEq (result1, result2, pos)


  (* Translators *)
  fun transDec (venv, tenv, level, breakpoint) =
    (* Typecheck an Absyn.dec *)
    let
      fun trdec (A.VarDec { name, escape, typ = NONE, init, pos }) =
            let
              val { exp, ty } = transExp (venv, tenv, level, breakpoint) init
              val venv' =
                Symbol.enter
                  ( venv
                  , name
                  , Env.VarEntry
                    { ty = ty
                    , access = Translate.allocLocal level (!escape)
                    }
                  )
            in
              { venv = venv'
              , tenv = tenv
              , exps =
                  [ ( Tr.assignExp
                      ( #exp
                          ( transExp ( venv', tenv, level, breakpoint )
                              ( A.VarExp ( A.SimpleVar ( name, pos ) ) )
                          )
                      , exp
                      )
                    )
                  ]
              }
            end
        | trdec (A.VarDec { name, escape, typ = SOME (tySym, _), init, pos }) =
            let
              fun venv' ty =
                Symbol.enter
                  ( venv
                  , name
                  , Env.VarEntry
                    { ty = ty
                    , access = Translate.allocLocal level (!escape)
                    }
                  )
            in
              (case Symbol.look (tenv, tySym) of
                NONE =>
                  (error pos "undefined type"; { venv = venv, tenv = tenv, exps = [] })
              | SOME ty =>
                  { venv = venv' ty
                  , tenv = tenv
                  , exps =
                      [ #exp
                        ( transExp ( venv' ty, tenv, level, breakpoint )
                          ( A.AssignExp
                            { var = A.SimpleVar (name, pos)
                            , exp = init
                            , pos = pos
                            }
                          )
                        )
                      ]
                  }
              )
            end

        | trdec (A.TypeDec decs) =
            let
              val tenv' =
                List.foldr
                  (fn (ty, env) =>
                    Symbol.enter (env, #name ty, T.NAME (#name ty, ref NONE)))
                  tenv decs
            in
              { venv = venv
              , tenv = List.foldr
                  (fn (ty, env) => Symbol.enter (env, #name ty, transTy (env, ty)))
                  tenv' decs
              , exps = []
              }
            end
        | trdec (A.FunctionDec decs) =
            let
              val venv' =
                List.foldr
                  (fn (dec, env) => Symbol.enter (env, #name dec, functionHeader (tenv, level, dec)))
                  venv decs
              fun runDec dec =
                case Symbol.look (venv', #name dec) of
                  NONE =>
                    ErrorMsg.impossible "Semantic Analysis did not find function header"
                | SOME (Env.FunEntry entry) =>
                    transFun (venv', tenv, entry, breakpoint, dec)
                | _ =>
                    ErrorMsg.impossible "Semantic Analysis found variable instead of function header"
            in
              List.map runDec decs;
              { tenv = tenv
              , venv = venv'
              , exps = []
              }
            end
    in
      trdec
    end
  and transTy (tenv, { name, ty = A.NameTy (sym, symPos), pos }) =
        T.NAME (sym, ref (Symbol.look (tenv, sym)))
    | transTy (tenv, { name, ty = A.RecordTy fields, pos }) =
        let
          fun getFieldType { name, typ, pos, escape } =
            case Symbol.look (tenv, typ) of
              NONE =>
                (error pos "undefined type"; NONE)
            | SOME ty =>
                SOME (name, ty)
        in
          T.RECORD ( List.mapPartial getFieldType fields, ref () )
        end
    | transTy (tenv, { name, ty = A.ArrayTy (sym, symPos), pos }) =
        (case Symbol.look (tenv, sym) of
           NONE =>
             (error symPos "undefined type"; T.NIL)
         | SOME ty =>
             T.ARRAY (ty, ref ()))
  and functionHeader (tenv, level, { name, params, result, body, pos }) =
    (* Return a Function's Type Heading *)
    let
      val params' =
        List.map #ty
          (List.map (transParam tenv) params)
      val label =
        Temp.newlabel ()
      val level' =
        Translate.newLevel
          { parent = level
          , name = label
          , formals = List.map (fn p => !(#escape p)) params
          }
    in
      (case result of
         SOME (sym, pos) =>
           (case Symbol.look (tenv, sym) of
              NONE =>
                (error pos "undefined type";
                 Env.FunEntry
                  { formals = params'
                  , result = T.UNIT
                  , level = level'
                  , label = label
                  })
            | SOME resTy =>
                Env.FunEntry
                  { formals = params'
                  , result = resTy
                  , level = level'
                  , label = label
                  }
           )
       | NONE =>
           Env.FunEntry
            { formals = params'
            , result = T.UNIT
            , level = level'
            , label = label
            }
      )
    end
  and transFun (venv, tenv, entry, breakpoint, { name, params, result = SOME (result, resultPos), body, pos }) =
        (case Symbol.look (tenv, result) of
           NONE =>
             (error resultPos "result type is undefined")
         | SOME resultTy =>
             let
               val params' =
                 List.map (transParam tenv) params
               fun addparam ({ name, ty, escape }, env) =
                 Symbol.enter
                  ( env
                  , name
                  , Env.VarEntry
                    { ty = ty
                    , access = Translate.allocLocal (#level entry) (!escape)
                    }
                  )
               val expResult =
                 transExp (List.foldr addparam venv params', tenv, (#level entry), breakpoint) body
               val entry =
                 case Symbol.look (venv, name) of
                   NONE =>
                     ErrorMsg.impossible "Semant.transFun could not find function header"
                 | SOME (Env.FunEntry e) =>
                     e
                 | _ =>
                     ErrorMsg.impossible "Semant.transFun found variable instead of function header"
             in
               checkSame ({ exp = (), ty = resultTy }, expResult, pos);
               Tr.functionDec (#label entry, #level entry, #exp expResult)
             end
        )
    | transFun (venv, tenv, entry, breakpoint, { name, params, result = NONE, body, pos }) =
        let
          val params' =
            List.map (transParam tenv) params
          fun addparam ({ name, ty, escape }, env) =
            Symbol.enter
              ( env
              , name
              , Env.VarEntry
                { ty = ty
                , access = Translate.allocLocal (#level entry) (!escape)
                }
              )
        in
          Tr.functionDec
            ( #label entry
            , #level entry
            , #exp (transExp (List.foldr addparam venv params', tenv, (#level entry), breakpoint) body)
            )
        end
  and transParam tenv { name, escape, typ = typSym, pos } =
        (* Typecheck a Function Parameter Declaration *)
        case Symbol.look (tenv, typSym) of
          NONE =>
            (error pos "undefined paramter type"; { name = name, ty = T.NIL, escape = escape })
        | SOME ty =>
            { name = name, ty = ty, escape = escape }
  and transExp (venv, tenv, level, breakpoint) =
    (* Typecheck an Absyn.exp *)
    let
      fun trexp (A.IntExp i) =
            { exp = Tr.intExp i, ty = T.INT }
        | trexp (A.StringExp (s, pos)) =
            { exp = Tr.stringExp s, ty = T.STRING }
        | trexp (A.VarExp var) =
            trvar var
        | trexp (A.NilExp) =
            { exp = Tr.nilExp, ty = T.NIL }
        | trexp (A.OpExp opExp) =
            transOp opExp
        | trexp (A.CallExp { func, args, pos }) =
            (case Symbol.look (venv, func) of
               NONE =>
                 (error pos "undefined function"; { exp = Tr.nilExp, ty = T.NIL })
             | SOME (Env.FunEntry { formals, result, label, level = funcLevel }) =>
                 if List.length args <> List.length formals then
                    (error pos "wrong number of arguments"; { exp = Tr.nilExp, ty = result })
                 else
                    { exp =
                        Tr.callExp
                          ( label
                          , funcLevel
                          , ListPair.map
                              (fn (exp, frm) =>
                                let val exp' = trexp exp
                                in (checkSame ({ exp = (), ty = actual_ty frm }, { exp = (), ty = actual_ty (#ty exp') }, pos);
                                    #exp exp')
                                end)
                              (List.rev args, formals)
                          , level)
                    , ty = result
                    }
             | SOME (Env.VarEntry _) =>
                (error pos "expecting a function"; { exp = Tr.nilExp, ty = T.NIL }))
        | trexp (A.RecordExp { fields, typ, pos }) =
            (case Symbol.look (tenv, typ) of
               NONE =>
                (error pos "undefined type"; { exp = Tr.nilExp, ty = T.NIL })
             | SOME (ty as (T.RECORD (tys, _))) =>
                (ListPair.map
                  (fn ((sym, exp, pos), (tySym, ty)) =>
                    if tySym = sym then
                      (checkSame ({ exp = (), ty = ty }, trexp exp, pos))
                    else
                      (error pos ("expecting `" ^ Symbol.name tySym ^ "`, given `" ^ Symbol.name sym ^ "`"))
                  ) (List.rev fields, tys);
                 { exp = Tr.recordExp (List.map (fn (_, e, _) => #exp (trexp e)) (List.rev fields))
                 , ty = ty }
                 )
             | SOME _ =>
                 (error pos "expecting a record"; { exp = Tr.nilExp, ty = T.NIL }))
        | trexp (A.SeqExp exps) =
            let
              fun runExps ((e, _), { lastTy, exps }) =
                let val { exp, ty } = trexp e
                in { exps = exp :: exps, lastTy = ty } end
            in
              (case exps of
                [] =>
                  { exp = Tr.nilExp, ty = T.UNIT }
              | xs =>
                  let val result = List.foldl runExps { exps = [], lastTy = T.NIL } xs
                  in { exp = Tr.seqExp (#exps result), ty = #lastTy result } end
              )
            end
        | trexp (A.AssignExp { var, exp, pos }) =
          let
            val varResult = trvar var
            val expResult = trexp exp
          in
            (checkSame ( { exp = (), ty = actual_ty (#ty varResult)}
                       , { exp = (), ty = actual_ty (#ty expResult)}, pos);
             { exp = Tr.assignExp (#exp varResult, #exp expResult), ty = T.UNIT })
          end
        | trexp (A.IfExp { test, then', else', pos }) =
            (case (trexp test, trexp then', Option.map trexp else') of
               ({ exp = testExp, ty = T.INT }, (thenRec as { exp = thenExp, ty = thenTy }), SOME (elseRec as { exp = elseExp, ty = elseTy })) =>
                 (checkSame (thenRec, elseRec, pos);
                  { exp = Tr.ifThenElseExp (testExp, thenExp, elseExp), ty = thenTy })
             | ({ exp = testExp, ty = T.INT }, thenExp, NONE) =>
                 (checkSame ({ exp = (), ty = T.UNIT }, thenExp, pos);
                  { exp = Tr.ifThenExp (testExp, #exp thenExp), ty = T.UNIT })
             | (testExp, _, _) =>
                 (error pos "test should be an integer";
                  { exp = Tr.nilExp, ty = T.UNIT }))
        | trexp (A.WhileExp { test, body, pos }) =
            let
              val doneBreakpoint = Tr.newBreakpoint ()
            in
              (case (trexp test, transExp (venv, tenv, level, SOME doneBreakpoint) body) of
                 ({ exp = testExp, ty = T.INT }, { exp = bodyExp, ty = T.UNIT }) =>
                   { exp = Tr.whileExp (testExp, bodyExp, doneBreakpoint), ty = T.UNIT }
               | ({ exp = _, ty = T.INT }, _) =>
                   (error pos "while body must produce no value";
                    { exp = Tr.nilExp, ty = T.UNIT })
               | _ =>
                   (error pos "while test must be an integer";
                    { exp = Tr.nilExp, ty = T.UNIT })
              )
            end
        | trexp (A.ForExp { var, lo, hi, body, pos, escape }) =
            let
              val limitSymbol =
                Symbol.symbol "TIGERCOMPILERFORLOOPLIMIT"
              val decs =
                [ A.VarDec
                    { name = var, escape = escape, pos = pos
                    , typ = SOME (Symbol.symbol "int", pos), init = lo
                    }
                , A.VarDec
                    { name = limitSymbol, escape = ref false, pos = pos
                    , typ = SOME (Symbol.symbol "int", pos), init = hi
                    }
                ]
              val exp =
                A.WhileExp
                  { test =
                      A.OpExp
                        { left = A.VarExp (A.SimpleVar (var, pos))
                        , right = A.VarExp (A.SimpleVar (limitSymbol, pos))
                        , oper = A.LeOp
                        , pos = pos
                        }
                  , body =
                    A.SeqExp
                      [ (body, pos)
                      , ( A.AssignExp
                            { var = A.SimpleVar (var, pos)
                            , exp =
                                A.OpExp
                                  { left = A.VarExp (A.SimpleVar (var, pos))
                                  , right = A.IntExp 1
                                  , oper = A.PlusOp
                                  , pos = pos
                                  }
                            , pos = pos
                            }
                        , pos
                        )
                      ]
                  , pos = pos
                  }
            in
              trexp (A.LetExp { decs = decs, body = exp, pos = pos })
            end
        | trexp (A.BreakExp pos) =
            (case breakpoint of
               SOME bp =>
                { exp = Tr.breakExp bp, ty = T.UNIT}
             | NONE =>
                (error pos "`break` must be in a `for` or `while` expression";
                 { exp = Tr.nilExp, ty = T.UNIT })
             )
        | trexp (A.ArrayExp { typ, size, init, pos }) =
            (case Symbol.look (tenv, typ) of
               NONE =>
                (error pos "undefined type"; { exp = Tr.nilExp, ty = T.UNIT })
             | SOME arrayTy =>
                 let
                   val sizeExp = trexp size
                   val initExp = trexp init
                 in
                  (checkSame ( { exp = (), ty = actual_ty arrayTy }
                             , { exp = (), ty = T.ARRAY (actual_ty (#ty initExp), ref ()) }
                             , pos);
                   checkInt ({ exp = (), ty = actual_ty (#ty sizeExp) }, pos);
                   { exp = Tr.arrayExp (#exp sizeExp, #exp initExp), ty = arrayTy })
                 end
            )
        | trexp (A.LetExp { decs, body, pos }) =
            let
              fun reducer (dec, { venv, tenv, exps }) =
                let val result = transDec (venv, tenv, level, breakpoint) dec
                in  { venv = #venv result, tenv = #tenv result, exps = #exps result @ exps } end
              val { venv = venv', tenv = tenv', exps } =
                List.foldl reducer { venv = venv, tenv = tenv, exps = [] } decs
              val bodyExp = transExp (venv', tenv', level, breakpoint) body
            in
              { exp = Tr.letExp (exps, #exp bodyExp), ty = #ty bodyExp }
            end
      and transOp { left, right, pos, oper } =
        let
          val leftExp = trexp left
          val rightExp = trexp right
        in
          case oper of
            A.PlusOp =>
              (checkBothInt (leftExp, rightExp, pos);
               { exp = Tr.intOpExp (#exp leftExp, #exp rightExp, oper), ty = T.INT })
          | A.MinusOp =>
              (checkBothInt (leftExp, rightExp, pos);
               { exp = Tr.intOpExp (#exp leftExp, #exp rightExp, oper), ty = T.INT })
          | A.TimesOp =>
              (checkBothInt (leftExp, rightExp, pos);
               { exp = Tr.intOpExp (#exp leftExp, #exp rightExp, oper), ty = T.INT })
          | A.DivideOp =>
              (checkBothInt (leftExp, rightExp, pos);
               { exp = Tr.intOpExp (#exp leftExp, #exp rightExp, oper), ty = T.INT })
          | A.LtOp =>
              let
                val result =
                  case #ty leftExp of
                    T.INT =>
                      Tr.intCondExp (#exp leftExp, #exp rightExp, oper)
                  | T.STRING =>
                      Tr.stringCondExp (#exp leftExp, #exp rightExp, oper)
                  | _ =>
                      Tr.nilExp
              in
                (checkBothIntOrString (leftExp, rightExp, pos);
                 { exp = result, ty = T.INT })
              end
          | A.LeOp =>
              let
                val result =
                  case #ty leftExp of
                    T.INT =>
                      Tr.intCondExp (#exp leftExp, #exp rightExp, oper)
                  | T.STRING =>
                      Tr.stringCondExp (#exp leftExp, #exp rightExp, oper)
                  | _ =>
                      Tr.nilExp
              in
                (checkBothIntOrString (leftExp, rightExp, pos);
                 { exp = result, ty = T.INT })
              end
          | A.GtOp =>
              let
                val result =
                  case #ty leftExp of
                    T.INT =>
                      Tr.intCondExp (#exp leftExp, #exp rightExp, oper)
                  | T.STRING =>
                      Tr.stringCondExp (#exp leftExp, #exp rightExp, oper)
                  | _ =>
                      Tr.nilExp
              in
                (checkBothIntOrString (leftExp, rightExp, pos);
                 { exp = result, ty = T.INT })
              end
          | A.GeOp =>
              let
                val result =
                  case #ty leftExp of
                    T.INT =>
                      Tr.intCondExp (#exp leftExp, #exp rightExp, oper)
                  | T.STRING =>
                      Tr.stringCondExp (#exp leftExp, #exp rightExp, oper)
                  | _ =>
                      Tr.nilExp
              in
                (checkBothIntOrString (leftExp, rightExp, pos);
                 { exp = result, ty = T.INT })
              end
          | A.EqOp =>
              let
                val result =
                  case #ty leftExp of
                    T.INT =>
                      Tr.intCondExp (#exp leftExp, #exp rightExp, oper)
                  | T.STRING =>
                      Tr.stringCondExp (#exp leftExp, #exp rightExp, oper)
                  | T.ARRAY _ =>
                      Tr.arrayRecordEqualityExp (#exp leftExp, #exp rightExp, oper)
                  | T.RECORD _ =>
                      Tr.arrayRecordEqualityExp (#exp leftExp, #exp rightExp, oper)
                  | _ =>
                      Tr.nilExp
              in
                (checkBothEq (leftExp, rightExp, pos);
                 { exp = result, ty = T.INT }
                )
              end
          | A.NeqOp =>
              let
                val result =
                  case #ty leftExp of
                    T.INT =>
                      Tr.intCondExp (#exp leftExp, #exp rightExp, oper)
                  | T.STRING =>
                      Tr.stringCondExp (#exp leftExp, #exp rightExp, oper)
                  | T.ARRAY _ =>
                      Tr.arrayRecordEqualityExp (#exp leftExp, #exp rightExp, oper)
                  | T.RECORD _ =>
                      Tr.arrayRecordEqualityExp (#exp leftExp, #exp rightExp, oper)
                  | _ =>
                      Tr.nilExp
              in
                (checkBothEq (leftExp, rightExp, pos);
                 { exp = result, ty = T.INT }
                )
              end
        end
      and trvar (A.SimpleVar (id, pos)) =
            ( case Symbol.look (venv, id) of
               NONE =>
                (error pos ("undefined variable `" ^ Symbol.name id ^ "`" );
                  { exp = Tr.nilExp, ty = T.INT })
             | SOME (Env.VarEntry { ty, access }) =>
                { exp = Tr.simpleVar (access, level), ty = actual_ty ty }
             | SOME _ =>
                (error pos "expecting a variable, not a function";
                 { exp = Tr.nilExp, ty = T.INT })
            )
        | trvar (A.FieldVar (var, id, pos)) =
            let
              val { exp, ty } = trvar var
              fun fieldResult record (acc, fs) =
                case fs of
                  [] =>
                    (error pos ("field `" ^ Symbol.name id ^ "` is not a member of that record type" );
                     { exp = Tr.nilExp, ty = record })
                | (s, t) :: rest =>
                    if (s = id) then
                      { exp = Tr.fieldVar (exp, acc), ty = t }
                    else
                      fieldResult record (acc + 1, rest)
            in
              case actual_ty ty of
                (record as (T.RECORD (fields, _))) =>
                  (fieldResult record (0, fields))
              | _ =>
                  (error pos "expecting a record variable"; { exp = Tr.nilExp, ty = T.INT })
            end
        | trvar (A.SubscriptVar (var, exp, pos)) =
            let
              val { exp = varExp, ty } = trvar var
            in
              case actual_ty ty of
                (array as (T.ARRAY (arrayTy, _))) =>
                  { exp = Tr.subscriptVar (varExp, #exp (trexp exp)), ty = arrayTy }
              | _ =>
                  (error pos "expecting an array variable";
                   { exp = Tr.nilExp, ty = T.INT })
            end
      and actual_ty ty =
        case ty of
          T.NAME (sym, opTy) =>
            (case !opTy of
              NONE =>
                (case Symbol.look (tenv, sym) of
                   NONE =>
                    ty
                 | SOME ty' =>
                     (opTy := SOME ty';
                      actual_ty ty')
                )
            | SOME ty =>
                actual_ty ty
            )
        | T.ARRAY (ty', r) =>
            T.ARRAY (actual_ty ty', r)
        | _ =>
            ty
    in
      trexp
    end

  (* Typecheck an Entire Program *)
  fun transProg exp = let
    val result =
      transExp
        ( Env.base_venv
        , Env.base_tenv
        , Translate.newLevel
          { parent = Translate.outermost
          , name = Temp.newlabel ()
          , formals = []
          }
        , NONE
        )
        exp
  in Translate.getResult () end

end
