-- traits, one day? :)

mod io = {
   external print : str -> () = "$print"
   external println : str -> () = "$println"
}

mod i32 = {
   external (+) : i32 -> i32 -> i32 = "$i32_add"
   external (==) : i32 -> i32 -> bool = "$i32_eq"
   external to_str : i32 -> str = "$i32_to_str"    
}

mod bool = {
   external (==) : bool -> bool -> bool = "$bool_eq"
   val to_str b = case b {
      true  => "true",
      false => "false",
   }
}

mod vec = import "vec.fth"
mod list = import "list.fth"
mod option = import "option.fth"
mod either = import "either.fth"

val id x = x
