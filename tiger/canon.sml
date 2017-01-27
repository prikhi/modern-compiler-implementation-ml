signature CANON = sig
  val linearize : Tree.stm -> Tree.stm list
  val basicBlocks : Tree.stm list -> (Tree.stm list list * Tree.label)
  val traceSchedule : Tree.stm list list * Tree.label -> Tree.stm list
end

structure Canon : CANON = struct
  structure T = Tree

  fun commute (stm, exp) =
    case (stm, exp) of
      (T.EXP (T.CONST _), _) =>
        true
    | (_, T.NAME _) =>
        true
    | (_, T.CONST _) =>
        true
    | _ =>
        false

  val noop = T.EXP (T.CONST 0)
  fun join (T.EXP (T.CONST _), x) = x
    | join (x, T.EXP (T.CONST _)) = x
    | join (x, y) = T.SEQ (x, y)

  fun do_stm (stm) = 
    case stm of
      T.SEQ (stm1, stm2) =>
        join (do_stm stm1, do_stm stm2)
    | T.JUMP (e, ls) =>
        reorder_stm ([e], fn [e] => T.JUMP (e, ls))
    | T.CJUMP (p, e1, e2, t, f) =>
        reorder_stm ([e1, e2], fn [e1, e2] => T.CJUMP (p, e1, e2, t, f))
    | T.MOVE (T.TEMP t, T.CALL (a, bs)) =>
        reorder_stm (a::bs, fn a::bs => T.MOVE (T.TEMP t, T.CALL (a, bs)))
    | T.MOVE (T.TEMP t, b) =>
        reorder_stm ([b], fn [b] => T.MOVE (T.TEMP t, b))
    | T.MOVE (T.MEM a, b) =>
        reorder_stm ([a, b], fn [a, b] => T.MOVE (T.MEM a, b))
    | T.MOVE (T.ESEQ (s, e), b) =>
        do_stm (T.SEQ (s, T.MOVE (e, b)))
    | T.EXP (T.CALL (a, bs)) =>
        reorder_stm (a::bs, fn a::bs => T.EXP (T.CALL (a, bs)))
    | T.EXP e =>
        reorder_stm ([e], fn [e] => T.EXP e)
    | _ =>
        stm
  and do_exp (exp) =
    case exp of
      T.BINOP (p, a, b) =>
        reorder_exp([a, b], fn [a, b] => T.BINOP (p, a, b))
    | T.MEM a =>
        reorder_exp([a], fn [a] => T.MEM a)
    | T.ESEQ (a, b) =>
        let 
          val stms = do_stm a
          val (stms', e) = do_exp b
        in 
          (join (stms, stms'), e)
        end
    | T.CALL (a, bs) =>
        reorder_exp(a::bs, fn a::bs => T.CALL (a, bs))
    | _ =>
        (noop, exp)
  (* from book code *)
  and reorder ((e as T.CALL _ )::rest) =
	let val t = Temp.newtemp()
	 in reorder(T.ESEQ(T.MOVE(T.TEMP t, e), T.TEMP t) :: rest)
	end
    | reorder (a::rest) =
	 let val (stms,e) = do_exp a
	     val (stms',el) = reorder rest
	  in if commute(stms',e)
	     then (join(stms , stms'),e::el)
	     else let val t = Temp.newtemp()
		   in (join (join (stms , T.MOVE(T.TEMP t, e)),  stms'), T.TEMP t :: el)
		  end
	 end
    | reorder nil = (noop,nil)
  and reorder_exp(el,build) = let val (stms,el') = reorder el
                        in (stms, build el')
                       end
  and reorder_stm(el,build) = let val (stms,el') = reorder (el)
		 	 in join(stms , build(el'))
			end
  (* book code finished *)
  (* TODO: write own reorders *)


  fun linear (T.SEQ (a, b), l) =
        linear (a, linear (b, l))
    | linear (c, l) =
        c :: l

  fun linearize s =
    linear (s, [])


  type block = Tree.stm list

  fun basicBlocks initialBlock = 
    let
      val doneLabel = Temp.newlabel ()

      fun run (stms, current, finished) : block list =
        case stms of
          ((s as T.JUMP _) :: ss) =>
            run (ss, [], (List.rev (s :: current)) :: finished)
        | ((s as T.CJUMP _) :: ss) =>
            run (ss, [], (List.rev (s :: current)) :: finished)
        | ((s as T.LABEL l) :: ss) =>
            run (ss, [T.LABEL l], (List.rev (T.JUMP (T.NAME l, [l]) :: current)) :: finished)
        | (s::ss) =>
            run (ss, s :: current, finished)
        | [] =>
            List.rev ((List.rev (T.JUMP (T.NAME doneLabel, [doneLabel]) :: current)) :: finished)
    in
      case initialBlock of
        ((s as T.LABEL _) :: ss) =>
          (run (ss, [s], []), doneLabel)
      | _ =>
          (run (initialBlock, [T.LABEL (Temp.newlabel ())], []), doneLabel)
    end

  (* from book code *)
  fun enterblock(b as (T.LABEL s :: _), table) = Symbol.enter(table,s,b)
    | enterblock(_, table) = table

  fun splitlast([x]) = (nil,x)
    | splitlast(h::t) = let val (t',last) = splitlast t in (h::t', last) end

  fun trace(table,b as (T.LABEL lab :: _),rest) = 
   let val table = Symbol.enter(table, lab, nil)
    in case splitlast b
     of (most,T.JUMP(T.NAME lab, _)) =>
	  (case Symbol.look(table, lab)
            of SOME(b' as _::_) => most @ trace(table, b', rest)
	     | _ => b @ getnext(table,rest))
      | (most,T.CJUMP(opr,x,y,t,f)) =>
          (case (Symbol.look(table,t), Symbol.look(table,f))
            of (_, SOME(b' as _::_)) => b @ trace(table, b', rest)
             | (SOME(b' as _::_), _) => 
		           most @ [T.CJUMP(T.notRel opr,x,y,f,t)]
		                @ trace(table, b', rest)
             | _ => let val f' = Temp.newlabel()
		     in most @ [T.CJUMP(opr,x,y,t,f'), 
				T.LABEL f', T.JUMP(T.NAME f,[f])]
			     @ getnext(table,rest)
                        end)
      | (most, T.JUMP _) => b @ getnext(table,rest)
     end

  and getnext(table,(b as (T.LABEL lab::_))::rest) = 
           (case Symbol.look(table, lab)
             of SOME(_::_) => trace(table,b,rest)
              | _ => getnext(table,rest))
    | getnext(table,nil) = nil

  fun traceSchedule(blocks,done) = 
       getnext(foldr enterblock Symbol.empty blocks, blocks)
         @ [T.LABEL done]
  (* book code finished *)


  (* TODO: finish own tracer
  fun traceSchedule (blocks, doneLabel) =
    let
      fun runTrace (stms, table, results) =
        case stms of 
          [] =>
            { stms = List.rev results, table = table }
        | (s as T.JUMP (T.NAME l, _)) :: [] =
            (case Symbol.look (table, l) of
               SOME _ =>
                results

            )
        | (s as T.LABEL l) :: rest =>
            runTrace (rest, Symbol.enter (table, l, ()), s :: results)
        | x :: xs =>
            runTrace (xs, table, x :: results)


      fun trace (toProcess, table, finishedTraces) : block =
        case toProcess of
          [] =>
            List.foldl op@ [] finishedTraces
        | (b as (T.LABEL l) :: _) :: rest =>
            (case Symbol.look (table, l) of
               NONE =>
                let val result = runTrace (b, table)
                in  trace (rest, #table result, (#stms result) :: finishedTraces) end
             | SOME _ =>
                 trace (rest, table, finishedTraces)
            )

    in
      trace (blocks, Symbol.empty, []) @ [T.LABEL doneLabel]
    end
  *)
end
