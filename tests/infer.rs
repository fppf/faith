// FIXME tests are broken, need to add way to query HirCtxt for type from path

use driver::{Mode, Pass, Source};

fn infer(top_level: &str, main: &str) -> String {
    let src = format!(
        r#"
        {top_level}
        main = {main}
        "#
    );

    driver::run(Source::Str(src), Mode::Test, Pass::Infer);
    driver::get_buffer()
}

macro_rules! infer_ok {
    ($name:ident, $top_level:expr, $main:expr, $expected:expr) => {
        #[test]
        fn $name() {
            let buf = infer($top_level, $main);
            assert!(buf.contains($expected));
            assert!(false); // see FIXME
        }
    };
    ($name:ident, $main:expr, $expected:expr) => {
        #[test]
        fn $name() {
            let buf = infer("", $main);
            assert!(buf.contains($expected));
            assert!(false); // see FIXME
        }
    };
}

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
    module_empty,
    "mod m = {}",
    "()",
    "()"
}

infer_ok! {
    module_single_value,
    r"
       mod m = {
          val x = ()
       }
    ",
    "m.x",
    "()"
}

infer_ok! {
    module_nested,
    r"
       mod m = {
          mod n = {
             val id x = x       
          }
          val y = n.id
       }
    ",
    "m.y",
    "'a -> 'a"
}

infer_ok! {
    ref_val_from_enclosing_mod,
    r"
       mod m = {
           val x = false
           mod n = {
               mod o = {
                   val y = x
               }
           }
       }
    ",
    "m.n.y",
    "bool"
}

infer_ok! {
    simple_shadowing,
    "let x = 0 in let x = true in x",
    "bool"
}

infer_ok! {
    sequenced_let_shadowing,
    "let x = (), x = true in x",
    "bool"
}

infer_ok! {
    copy_shadowing,
    "let x = () in let x = x in x",
    "()"
}

infer_ok! {
    branch_shadowing,
    "let x = 0 in if true then let x = true in x else false; x",
    "i32"
}
