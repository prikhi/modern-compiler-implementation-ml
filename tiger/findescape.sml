structure FindEscape : sig
  val findEscape : Absyn.exp -> unit

  type depth
  type escEnv

  val traverseVar : escEnv * depth * Absyn.var -> unit
  val traverseExp : escEnv * depth * Absyn.exp -> unit
  val traverseDecs : escEnv * depth * Absyn.dec list -> escEnv
  val traverseDec : escEnv * depth -> Absyn.dec -> escEnv
end = struct
  structure A = Absyn

  type depth = int
  type escEnv = (depth * bool ref) Symbol.table

  fun findEscape exp =
    traverseExp (Symbol.empty, 0, exp)

  and traverseExp (env, depth, exp) =
    case exp of
      A.VarExp var =>
        traverseVar (env, depth, var)
    | A.NilExp =>
        ()
    | A.IntExp _ =>
        ()
    | A.StringExp _ =>
        ()
    | A.CallExp { args, ... } =>
        (List.map (fn arg => traverseExp (env, depth, arg)) args; ())
    | A.OpExp { left, right, ... } =>
        (traverseExp (env, depth, left);
         traverseExp (env, depth, right))
    | A.RecordExp { fields, ... } =>
        (List.map (fn (_, e, _) => traverseExp (env, depth, e)) fields; ())
    | A.SeqExp exps =>
        (List.map (fn (e, _) => traverseExp (env, depth, e)) exps; ())
    | A.AssignExp { var, exp, ... } =>
        (traverseVar (env, depth, var);
         traverseExp (env, depth, exp))
    | A.IfExp { test, then', else', ... } =>
        (traverseExp (env, depth, test);
         Option.map (fn e => traverseExp (env, depth, e)) else';
         traverseExp (env, depth, then'))
    | A.WhileExp { test, body, ... } =>
        (traverseExp (env, depth, test);
         traverseExp (env, depth, body))
    | A.ForExp { var, escape, lo, hi, body, ... } =>
        let
          val env' =
            Symbol.enter (env, var, (depth, escape))
        in
            traverseExp (env, depth, lo);
            traverseExp (env, depth, hi);
            traverseExp (env', depth, body)
        end
    | A.BreakExp _ =>
        ()
    | A.LetExp { decs, body, ... } =>
        let
          val env' =
            traverseDecs (env, depth, decs)
        in
          traverseExp (env', depth, body)
        end
    | A.ArrayExp { size, init, ... } =>
        (traverseExp (env, depth, size);
         traverseExp (env, depth, init))

  and traverseVar (env, depth, var) =
    case var of
      A.SimpleVar (sym, _) =>
        (case Symbol.look (env, sym) of
           NONE =>
            ()
         | SOME (d, escape) =>
             if depth > d then
               escape := true
             else
               ()
        )
    | A.FieldVar (v, _, _) =>
        traverseVar (env, depth, v)
    | A.SubscriptVar (v, exp, _) =>
        (traverseExp (env, depth, exp);
         traverseVar (env, depth, v))

  and traverseDecs (env, depth, decs) =
    List.foldr (fn (dec, env') => traverseDec (env', depth) dec) env decs

  and traverseDec (env, depth) dec =
    case dec of
      A.TypeDec decs =>
        env
    | A.VarDec { name, escape, init, ... } =>
        (escape := false;
         traverseExp (env, depth, init);
         Symbol.enter (env, name, (depth, escape)))
    | A.FunctionDec decs =>
        let
          fun traverse ({ name, params, body, pos, result }, env') =
            let
              fun addparam ({ name, escape, typ, pos }, env'') =
                (escape := false;
                 Symbol.enter (env'', name, (depth + 1, escape)))
              val env'' =
                List.foldr addparam env' params
            in
              traverseExp (env'', depth + 1, body);
              env'
            end
        in
          List.foldr traverse env decs
        end

end
