signature SET = sig
  type el
  type set
  val empty : set
  val member : set -> el -> bool
  val add : set -> el -> set
  val remove : set -> el -> set
  val union : set -> set -> set
  val difference : set -> set -> set
end

(* A Simple Integer Set for use in Graph Coloring *)
structure IntSet : SET = struct
  type el = int
  datatype set
    = Empty
    | Tree of set * el * set
  val empty =
    Empty
  fun add set x =
    case set of
      Empty =>
        Tree (Empty, x, Empty)
    | Tree (left, y, right) =>
        if x = y then
          set
        else if x > y then
          Tree (left, y, add right x)
        else
          Tree (add left x, y, right)
  fun member set x =
    case set of
      Empty =>
        false
    | Tree (left, y, right) =>
        if x = y then
          true
        else if x > y then
          member right x
        else
          member left x
  fun union set1 set2 =
    case set2 of
      Empty =>
        set1
    | Tree (left, x, right) =>
        let
          val leftUnion = union set1 left
          val rightUnion = union leftUnion right
        in
          add rightUnion x
        end
  fun remove set x =
    case set of
      Empty =>
        Empty
    | Tree (left, y, right) =>
        if x = y then
          union left right
        else if x > y then
          Tree (left, y, remove right x)
        else
          Tree (remove left x, y, right)
  fun difference set1 set2 =
    case set2 of
      Empty =>
        set1
    | Tree (left, x, right) =>
        let 
          val leftDiff = difference set1 left
          val rightDiff = difference leftDiff right
        in
          remove rightDiff x
        end
end


(* A Simple Generic Set Implemented Via Lists *)
signature EQ_TYPE = sig
  type t 
  val eq : t -> t -> bool
end
functor ListSet ( structure E : EQ_TYPE ) : SET = struct
  type el = E.t
  type set = el list
  val empty =
    []
  fun member set x =
    Option.isSome (List.find (fn y => E.eq x y) set)
  fun add set x = 
    x :: set
  fun remove set x =
    List.filter (fn y => not (E.eq x y)) set
  fun union set1 set2 =
    List.foldr (fn (x, set) => add set x) set1 set2
  fun difference set1 set2 =
    List.foldr (fn (x, set) => remove set x) set1 set2
end
