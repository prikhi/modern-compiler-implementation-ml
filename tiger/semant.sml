structure Semant : sig
  type venv
  type tenv
  type expty

  val transProg : Absyn.exp -> unit
  val transExp : venv * tenv * Translate.level -> Absyn.exp -> expty
  val transDec : venv * tenv * Translate.level -> Absyn.dec -> {venv: venv, tenv: tenv}
  val transTy : tenv * { name : Absyn.symbol, ty : Absyn.ty, pos : Absyn.pos } -> Types.ty
  val transFun : venv * tenv * Translate.level * Absyn.fundec -> unit
end = struct
  (* Aliases *)
  structure A = Absyn
  structure T = Types
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
  fun transDec (venv, tenv, level) =
    (* Typecheck an Absyn.dec *)
    let
      fun trdec (A.VarDec { name, escape, typ = NONE, init, pos }) =
            let
              val { exp, ty } = transExp (venv, tenv, level) init
            in
              { venv =
                  Symbol.enter
                    ( venv
                    , name
                    , Env.VarEntry
                      { ty = ty
                      , access = Translate.allocLocal level (!escape)
                      }
                    )
              , tenv = tenv
              }
            end
        | trdec (A.VarDec { name, escape, typ = SOME (tySym, _), init, pos }) =
            (case Symbol.look (tenv, tySym) of
               NONE =>
                 (error pos "undefined type"; { venv = venv, tenv = tenv })
             | SOME ty =>
                 { venv =
                    Symbol.enter
                      ( venv
                      , name
                      , Env.VarEntry
                        { ty = ty
                        , access = Translate.allocLocal level (!escape)
                        }
                      )
                 , tenv = tenv
                 }
            )

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
                | SOME (Env.FunEntry { level, ... }) =>
                    transFun (venv', tenv, level, dec)
                | _ =>
                    ErrorMsg.impossible "Semantic Analysis found variable instead of function header"
            in
              List.map runDec decs;
              { tenv = tenv
              , venv = venv'
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
      val level' =
        Translate.newLevel
          { parent = level
          , name = (Temp.newlabel ())
          , formals = List.map (fn p => !(#escape p)) params
          }
      val label =
        Temp.newlabel ()
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
  and transFun (venv, tenv, level, { name, params, result = SOME (result, resultPos), body, pos }) =
        (case Symbol.look (tenv, result) of
           NONE =>
             (error resultPos "result type is undefined")
         | SOME resultTy =>
             let
               val params' =
                 List.map (transParam tenv) params
               fun addparam ({ name, ty }, env) =
                 Symbol.enter
                  ( env
                  , name
                  , Env.VarEntry
                    { ty = ty
                    , access = Translate.allocLocal level true
                    }
                  )
               val expResult =
                 transExp (List.foldr addparam venv params', tenv, level) body
             in
               checkSame ({ exp = (), ty = resultTy }, expResult, pos)
             end
        )
    | transFun (venv, tenv, level, { name, params, result = NONE, body, pos }) =
        let
          val params' =
            List.map (transParam tenv) params
          fun addparam ({ name, ty }, env) =
            Symbol.enter
              ( env
              , name
              , Env.VarEntry
                { ty = ty
                , access = Translate.allocLocal level true
                }
              )
        in
          transExp (List.foldr addparam venv params', tenv, level) body;
          ()
        end
  and transParam tenv { name, escape, typ = typSym, pos } =
        (* Typecheck a Function Parameter Declaration *)
        case Symbol.look (tenv, typSym) of
          NONE =>
            (error pos "undefined paramter type"; { name = name, ty = T.NIL })
        | SOME ty =>
            { name = name, ty = ty }
  and transExp (venv, tenv, level) =
    (* Typecheck an Absyn.exp *)
    let
      fun trexp (A.IntExp i) =
            { exp = (), ty = T.INT }
        | trexp (A.StringExp (s, pos)) =
            { exp = (), ty = T.STRING }
        | trexp (A.VarExp var) =
            trvar var
        | trexp (A.NilExp) =
            { exp = (), ty = T.NIL }
        | trexp (A.OpExp opExp) =
            transOp opExp
        | trexp (A.CallExp { func, args, pos }) =
            (case Symbol.look (venv, func) of
               NONE =>
                 (error pos "undefined function"; { exp = (), ty = T.NIL })
             | SOME (Env.FunEntry { formals, result, label, level }) =>
                (ListPair.map
                  (fn (exp, frm) =>
                    (checkSame ({ exp = (), ty = frm }, trexp exp, pos)))
                  (List.rev args, formals);
                 { exp = (), ty = result })
             | SOME (Env.VarEntry _) =>
                (error pos "expecting a function"; { exp = (), ty = T.NIL }))
        | trexp (A.RecordExp { fields, typ, pos }) =
            (case Symbol.look (tenv, typ) of
               NONE =>
                (error pos "undefined type"; { exp = (), ty = T.NIL })
             | SOME (ty as (T.RECORD (tys, _))) =>
                (ListPair.map
                  (fn ((sym, exp, pos), (tySym, ty)) =>
                    if tySym = sym then
                      (checkSame ({ exp = (), ty = ty }, trexp exp, pos))
                    else
                      (error pos ("expecting `" ^ Symbol.name tySym ^ "`, given `" ^ Symbol.name sym ^ "`"))
                  ) (List.rev fields, tys);
                 { exp = (), ty = ty })
             | SOME _ =>
                 (error pos "expecting a record"; { exp = (), ty = T.NIL }))
        | trexp (A.SeqExp exps) =
            (case exps of
               [] =>
                 { exp = (), ty = T.UNIT }
             | (exp, pos) :: [] =>
                 { exp = (), ty = #ty (trexp exp) }
             | (exp, pos) :: xs =>
                 (trexp exp;
                  trexp (A.SeqExp xs)))
        | trexp (A.AssignExp { var, exp, pos }) =
          let
            val varResult = trvar var
            val expResult = trexp exp
          in
            (checkSame (varResult, expResult, pos); { exp = (), ty = T.UNIT })
          end
        | trexp (A.IfExp { test, then', else', pos }) =
            (case (trexp test, trexp then', Option.map trexp else') of
               ({ exp = _, ty = T.INT }, (thenExp as { exp = _, ty = thenTy }), SOME elseExp) =>
                 (checkSame (thenExp, elseExp, pos);
                  { exp = (), ty = thenTy })
             | ({ exp = _, ty = T.INT }, thenExp, NONE) =>
                 (checkSame ({ exp = (), ty = T.UNIT }, thenExp, pos);
                  { exp = (), ty = T.UNIT })
             | (testExp, _, _) =>
                 (error pos "test should be an integer";
                  { exp = (), ty = T.UNIT }))
        | trexp (A.WhileExp { test, body, pos }) =
            (loopNesting := !loopNesting + 1;
             (case (trexp test, trexp body) of
               ({ exp = _, ty = T.INT }, { exp = _, ty = T.UNIT }) =>
                ()
             | ({ exp = _, ty = T.INT }, bodyExp) =>
                (error pos "while body must produce no value")
             | _ =>
                (error pos "while test must be an integer")
              );
              loopNesting := !loopNesting - 1;
              { exp = (), ty = T.UNIT })
        | trexp (A.ForExp { var, lo, hi, body, pos, escape }) =
            let
              val venv' =
                Symbol.enter
                  ( venv
                  , var
                  , Env.VarEntry
                    { ty = T.INT
                    , access = Translate.allocLocal level true
                    }
                  )
            in
              (checkInt (trexp lo, pos); checkInt (trexp hi, pos);
               loopNesting := !loopNesting + 1;
               checkSame ({ exp = (), ty = T.UNIT }, transExp (venv', tenv, level) body, pos);
               loopNesting := !loopNesting - 1;
               { exp = (), ty = T.UNIT }
              )
            end
        | trexp (A.BreakExp pos) =
            ((if !loopNesting > 0 then
                ()
              else
                (error pos "`break` must be in a `for` or `while` expression")
             );
             { exp = (), ty = T.UNIT })
        | trexp (A.ArrayExp { typ, size, init, pos }) =
            (case Symbol.look (tenv, typ) of
               NONE =>
                (error pos "undefined type"; { exp = (), ty = T.UNIT })
             | SOME arrayTy =>
                (checkSame ( { exp = (), ty = actual_ty arrayTy }
                           , { exp = (), ty = T.ARRAY (actual_ty (#ty (trexp init)), ref ()) }
                           , pos);
                 checkInt (trexp size, pos);
                 { exp = (), ty = arrayTy }))
        | trexp (A.LetExp { decs, body, pos }) =
            let
              val { venv = venv', tenv = tenv' } =
                List.foldl (fn (dec, { venv, tenv }) => transDec (venv, tenv, level) dec)
                  { venv = venv, tenv = tenv } decs

                val bodyExp = transExp (venv', tenv', level) body
            in
              { exp = (), ty = #ty bodyExp }
            end
      and transOp { left, right, pos, oper } =
        let
          val leftExp = trexp left
          val rightExp = trexp right
        in
          case oper of
            A.PlusOp =>
              (checkBothInt (leftExp, rightExp, pos);
               { exp = (), ty = T.INT })
          | A.MinusOp =>
              (checkBothInt (leftExp, rightExp, pos);
               { exp = (), ty = T.INT })
          | A.TimesOp =>
              (checkBothInt (leftExp, rightExp, pos);
               { exp = (), ty = T.INT })
          | A.DivideOp =>
              (checkBothInt (leftExp, rightExp, pos);
               { exp = (), ty = T.INT })
          | A.LtOp =>
              (checkBothIntOrString (leftExp, rightExp, pos);
               { exp = (), ty = T.INT })
          | A.LeOp =>
              (checkBothIntOrString (leftExp, rightExp, pos);
               { exp = (), ty = T.INT })
          | A.GtOp =>
              (checkBothIntOrString (leftExp, rightExp, pos);
               { exp = (), ty = T.INT })
          | A.GeOp =>
              (checkBothIntOrString (leftExp, rightExp, pos);
               { exp = (), ty = T.INT })
          | A.EqOp =>
              (checkBothEq (leftExp, rightExp, pos);
                { exp = (), ty = T.INT })
          | A.NeqOp =>
              (checkBothEq (leftExp, rightExp, pos);
                { exp = (), ty = T.INT })
        end
      and trvar (A.SimpleVar (id, pos)) =
            ( case Symbol.look (venv, id) of
               NONE =>
                (error pos ("undefined variable `" ^ Symbol.name id ^ "`" );
                  { exp = (), ty = T.INT })
             | SOME (Env.VarEntry { ty, access }) =>
                { exp = (), ty = actual_ty ty }
             | SOME _ =>
                (error pos "expecting a variable, not a function";
                 { exp = (), ty = T.INT })
            )
        | trvar (A.FieldVar (var, id, pos)) =
            let
              val { exp, ty } = trvar var
            in
              case actual_ty ty of
                (record as (T.RECORD (fields, _))) =>
                  (case List.filter (fn (s, t) => s = id) fields of
                     [] =>
                        (error pos ("field `" ^ Symbol.name id ^ "` is not a member of that record type" );
                         { exp = (), ty = record })
                   | (s, t) :: _ =>
                        { exp = (), ty = t })
              | _ =>
                  (error pos "expecting a record variable"; { exp = (), ty = T.INT })
            end
        | trvar (A.SubscriptVar (var, exp, pos)) =
            let
              val { exp, ty } = trvar var
            in
              case actual_ty ty of
                (array as (T.ARRAY (arrayTy, _))) =>
                  { exp = (), ty = arrayTy }
              | _ =>
                  (error pos "expecting an array variable"; { exp = (), ty = T.INT })
            end
      and actual_ty ty =
        case ty of
          T.NAME (sym, opTy) =>
            (case !opTy of
              NONE =>
                ty
            | SOME ty =>
                actual_ty ty
            )
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
        )
        exp
  in () end

end
