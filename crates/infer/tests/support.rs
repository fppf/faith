pub fn infer(top_level: &str, main: &str) -> String {
    let src = format!(
        r#"
        mod std = import "../../lib/std"
        {top_level}
        main = {main}
        "#
    );

    let ast_arena = syntax::Arena::default();
    let hir_arena = hir::Arena::default();
    let program = syntax::parse_str_program_in(&ast_arena, &src).unwrap();
    let program = hir::lower_program_in(&hir_arena, program).unwrap();
    let infer_data = infer::infer_program_in(&hir_arena, program).unwrap();
    let main = infer_data.expr_types.get(&program.main).unwrap();
    pp::desubscriptify(main.to_string())
}

#[macro_export]
macro_rules! infer_ok {
    ($name:ident, $top_level:expr, $main:expr, $typ:expr) => {
        #[test]
        fn $name() {
            let main_result = infer($top_level, $main);
            assert_eq!(main_result, $typ);
        }
    };
    ($name:ident, $main:expr, $typ:expr) => {
        #[test]
        fn $name() {
            let main_result = infer("", $main);
            assert_eq!(main_result, $typ);
        }
    };
}
