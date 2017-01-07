signature TABLE = 
sig
   type key
   type 'a table
   val empty : 'a table
   val enter : 'a table * key * 'a -> 'a table
   val look  : 'a table * key -> 'a option
   val entries : 'a table -> (key * 'a) list
end

