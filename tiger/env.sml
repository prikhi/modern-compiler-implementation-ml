signature ENV = sig
  type ty
  datatype enventry
    = VarEntry of
      { ty : ty
      , access : Translate.access
      }
    | FunEntry of
      { formals: ty list
      , result: ty
      , label : Temp.label
      , level : Translate.level
      }
  val base_tenv : ty Symbol.table
  val base_venv : enventry Symbol.table
end

structure Env : ENV = struct
  structure S = Symbol
  structure T = Types

  type ty = Types.ty
  datatype enventry
    = VarEntry of
      { ty : ty
      , access : Translate.access
      }
    | FunEntry of
      { formals: ty list
      , result: ty
      , label : Temp.label
      , level : Translate.level
      }

  val base_tenv =
    S.enter' S.empty
      [ (S.symbol "string", T.STRING)
      , (S.symbol "int", T.INT)
      ]
  val base_venv =
    S.enter' S.empty
      (List.map
        (fn (s, t) => ( Symbol.symbol s
                      , FunEntry
                        { formals = #formals t
                        , result = #result t
                        , level = Translate.outermost
                        , label = Temp.newlabel ()
                        }
                      ))
        [ ("print", { formals = [ T.STRING ], result = T.UNIT })
        , ("flush", { formals = [], result = T.UNIT })
        , ("getchar", { formals = [], result = T.STRING })
        , ("ord", { formals = [ T.STRING ], result = T.INT })
        , ("chr", { formals = [ T.INT ], result = T.STRING })
        , ("size", { formals = [ T.STRING ], result = T.INT })
        , ("substring", { formals = [ T.STRING, T.INT, T.INT ], result = T.STRING })
        , ("concat", { formals = [ T.STRING, T.STRING ], result = T.STRING })
        , ("not", { formals = [ T.INT ], result = T.INT })
        , ("exit", { formals = [ T.INT ], result = T.UNIT })
        ]
      )
end
