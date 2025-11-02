{-
   std.vec
   -------
   mutable vectors
-}

-- Creation

external empty : ['a] = "$vec_empty"
external single : 'a -> ['a] = "$vec_single"
external rep : i32 -> 'a -> ['a] = "$vec_rep"
external gen : i32 -> (i32 -> 'a) -> ['a] = "$vec_gen" 

-- Length

external len : ['a] -> i32 = "$vec_len"
external is_empty : ['a] -> bool = "$vec_is_empty"

-- Access

external at : ['a] -> i32 -> 'a = "$vec_at"
external head : ['a] -> 'a = "$vec_head"
external last : ['a] -> 'a = "$vec_last"

-- Operations

external map : ('a -> 'b) -> ['a] -> ['b] = "$vec_map"
external imap : (i32 -> 'a -> 'b) -> ['a] -> ['b] = "$vec_imap"

-- Modification

external push : 'a -> ['a] -> ['a] = "$vec_push"
