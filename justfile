alias c := compile
alias t := test

set positional-arguments

# run the faith compiler
compile *args='':
    cargo run --bin faithc -- "$@"

# run the faith compiler with debug tracing
trace *args='':
    FAITH_LOG=trace cargo run --bin faithc -- "$@"

# run the faith test suite
test:
    cargo build --bin faithc
    cargo run --bin run_tests -- ./target/debug/faithc ./tests
