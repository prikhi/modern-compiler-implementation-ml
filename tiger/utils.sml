structure ListUtils : sig
  val isMember : ''a -> ''a list -> bool
  val isMemberBy : ('a * 'a -> bool) -> 'a -> 'a list -> bool
  val difference : ''a list -> ''a list -> ''a list
  val differenceBy : ('a * 'a -> bool)-> 'a list -> 'a list -> 'a list
  val intersection : ''a list -> ''a list -> ''a list
  val intersectionBy : ('a * 'a -> bool) -> 'a list -> 'a list -> 'a list
end = struct
  fun isMember e l =
    Option.isSome (List.find (fn x => e = x) l)
  fun isMemberBy f e l =
    Option.isSome (List.find (fn x => f (e, x)) l)
  fun difference list1 list2 =
    List.foldr (fn (i, acc) => List.filter (fn x => i <> x) acc) list1 list2
  fun differenceBy f list1 list2 =
    List.foldr (fn (i, acc) => List.filter (fn x => not (f (i, x))) acc) list1 list2
  fun intersection list1 list2 =
    List.filter (fn i => isMember i list2) list1
  fun intersectionBy f list1 list2 =
    List.filter (fn i => isMemberBy f i list2) list1
end

structure GraphUtils : sig
  val getValue : 'a Graph.Table.table * Graph.Table.key * 'a -> 'a
  val getListValue : 'a list Graph.Table.table * Graph.Table.key -> 'a list
end = struct
  fun getValue (t, k, d) =
    case Graph.Table.look (t, k) of
      NONE =>
        d
    | SOME v =>
        v
  fun getListValue (t, k) =
    getValue (t, k, [])
end
