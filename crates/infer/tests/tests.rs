#[macro_use]
mod support;
use support::*;

infer_ok! {
    literals,
    r#"(1, (), -3, true, false, "aaaa")"#,
    "(i32, (), i32, bool, bool, str)"
}

infer_ok! {
    lambda_id,
    r"\x -> x",
    "'a -> 'a"
}

infer_ok! {
    lambda_ignore_argument,
    r"\_ -> ()",
    "'a -> ()"
}

infer_ok! {
    lambda_two_arguments_1,
    r"\x y -> x",
    "'a -> 'b -> 'a"
}

infer_ok! {
    lambda_two_arguments_2,
    r"\x y -> y",
    "'a -> 'b -> 'b"
}

infer_ok! {
    lambda_pair_argument,
    r"\(x, y) -> x",
    "('a, 'b) -> 'a"
}

infer_ok! {
    apply_id,
    r"(\x -> x) ()",
    "()"
}

infer_ok! {
    apply_one_argument,
    r"(\x y -> x) ()",
    "'a -> ()"
}

infer_ok! {
    apply_to_id,
    r"(\x y -> x) (\z -> z)",
    "'a -> 'b -> 'b"
}

infer_ok! {
    std_either_left,
    "use std.either ( either )",
    "Left ()",
    "either () 'a"
}

infer_ok! {
    std_option_some,
    "use std.option ( option )",
    "Some ()",
    "option ()"
}

infer_ok! {
    std_option_none,
    "use std.option ( option )",
    "None",
    "option 'a"
}

infer_ok! {
    vec_empty,
    "[]",
    "['a]"
}

infer_ok! {
    vec_bool,
    "[false, true]",
    "[bool]"
}

infer_ok! {
    vec_map_trivial,
    r"std.vec.map (\_ -> false) [0]",
    "[bool]"
}

infer_ok! {
    vec_map,
    "use std.either ( either, is_left )
     use std.vec ( map )",
    r"
      let v1 = [Left (), Right -1],
          v2 = map is_left v1
      in (v1, v2)
    ",
    "([either () i32], [bool])"
}

infer_ok! {
    module_nested,
    r"
       mod m = ({
           mod n = {
               val id x = x       
           }
           val y = n.id
       } : { val y : 'a -> 'a })
    ",
    "m.y ()",
    "()"
}
