alias c := compile
alias t := test

# run the faith compiler
compile FILE:
    cargo run --bin faithc -- {{FILE}}

# run the faith test suite
test:
    cargo build --bin faithc
    cargo run --bin run_tests -- ./target/debug/faithc ./tests

