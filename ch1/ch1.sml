(* Straight-Line Program Interpreter *)
type id = string
datatype binop = Plus | Minus | Times | Div
datatype stm = CompoundStm of stm * stm
             | AssignStm of id * exp
             | PrintStm of exp list
     and exp = IdExp of id
             | NumExp of int
             | OpExp of exp * binop * exp
             | EseqExp of stm * exp

val prog = CompoundStm (AssignStm ("a", OpExp (NumExp 5, Plus, NumExp 3)),
            CompoundStm (AssignStm ("b", EseqExp(PrintStm [IdExp "a", OpExp (IdExp "a", Minus, NumExp 1)],
                                                 OpExp (NumExp 10, Times, IdExp "a"))),
              PrintStm[IdExp "b"]))

fun explistargs el =
  (case el of
      [] => 0
    | (EseqExp (s, _)::es) =>
      Int.max (length el, Int.max (maxargs s, maxargs (PrintStm es)))
    | (_::es) => Int.max (length el, maxargs (PrintStm es)))
and maxargs (CompoundStm (s1, s2)) = Int.max (maxargs s1, maxargs s2)
    | maxargs (AssignStm (_, e)) = explistargs [e]
    | maxargs (PrintStm el) = explistargs el

fun interp s = let
  fun update (t, i, v) = (i, v)::t
  fun lookup ([], i) = raise Empty
    | lookup ((i1, v1)::ts, i) =
        if String.compare(i1, i) = EQUAL
        then v1
        else lookup (ts, i)
  fun interpStm (CompoundStm (s1, s2), t) = interpStm (s2, interpStm (s1, t))
    | interpStm (AssignStm (i, e), t) = let val (e', t') = interpExp (e, t)
                                        in update (t', i, e')
                                        end
    | interpStm (PrintStm [], t) = (print "\n"; t)
    | interpStm (PrintStm (e::es), t) =
        let val (e', t') = interpExp (e, t)
        in (print (Int.toString e' ^ " "); interpStm (PrintStm es, t))
        end
  and interpExp (IdExp i, t) = (lookup (t, i), t)
    | interpExp (NumExp x, t) = (x, t)
    | interpExp (OpExp (e1, b, e2), t) =
        let val (e1', t') = interpExp (e1, t)
            val (e2', t'') = interpExp (e2, t')
        in (interpBinop (e1', b, e2'), t'')
        end
    | interpExp (EseqExp (s, e), t) = interpExp (e, interpStm (s, t))
  and interpBinop (x, Plus, y) = x + y
    | interpBinop (x, Minus, y) = x - y
    | interpBinop (x, Times, y) = x * y
    | interpBinop (x, Div, y) = x div y
in
  interpStm (s, [])
end


(* Exercises *)
type key = string
datatype 'a tree = Leaf | Tree of 'a tree * key * 'a * 'a tree

val empty = Leaf

fun insert (Leaf, key, value) = Tree (Leaf, key, value, Leaf)
  | insert (Tree (left, treeKey, treeValue, right), key, value) =
      if key = treeKey
      then Tree (left, treeKey, value, right)
      else if key < treeKey
      then Tree (insert (left, key, value), treeKey, treeValue, right)
      else Tree (left, treeKey, treeValue, insert (right, key, value))

fun lookup (Leaf, key) = raise Empty
  | lookup (Tree (left, treeKey, treeValue, right), key) =
      if key = treeKey
      then treeValue
      else if key < treeKey
      then lookup (left, key)
      else lookup (right, key)

(* a b c d e f g
 * yields a tree with only right nodes:
 *
 *      Tree Leaf a (Tree Leaf b (... Leaf f (Tree Leaf g Leaf))...)
 *
 * t s p i p f b s t
 * yields a tree with many left nodes and few right nodes:
 *
 *      Tree (Tree (Tree (Tree (Tree Leaf b Leaf) i (Tree Leaf f Leaf)) p Leaf) s Leaf) t Leaf
 *)
