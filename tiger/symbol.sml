signature SYMBOL =
sig
  eqtype symbol
  val symbol : string -> symbol
  val name : symbol -> string
  type 'a table
  val empty : 'a table
  val enter : 'a table * symbol * 'a -> 'a table
  val enter' : 'a table -> (symbol * 'a) list -> 'a table
  val look  : 'a table * symbol -> 'a option
  val entries : 'a table -> (symbol * 'a) list
  val printEntries : 'a table -> unit
end

structure Symbol :> SYMBOL =
struct

  type symbol = string * int

  structure H = HashTable

  exception Symbol
  val nextsym = ref 0
  val sizeHint = 128
  val hashtable : (string,int) H.hash_table = 
		H.mkTable(HashString.hashString, op = ) (sizeHint,Symbol)
  
  fun symbol name =
      case H.find hashtable name
       of SOME i => (name,i)
        | NONE => let val i = !nextsym
	           in nextsym := i+1;
		      H.insert hashtable (name,i);
		      (name,i)
		  end

  fun name(s,n) = s

  structure Table = IntMapTable(type key = symbol
				fun getInt(s,n) = n
                fun getKey n = case List.find (fn (_, n') => n = n')
                                              (H.listItemsi hashtable) of
                                 SOME sym => sym
                               | NONE => raise Fail "not found")

  type 'a table= 'a Table.table
  val empty = Table.empty
  val enter = Table.enter
  fun enter' t es =
    List.foldr (fn ((sy, e), table) => enter (table, sy, e)) t es
  val look = Table.look
  val entries = Table.entries
  fun printEntries t =
    (List.map (fn (sy, _) => print (name sy ^ " ")) (entries t); print "\n"; ())
end
