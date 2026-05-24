c FILE:
    cargo run --bin faithc -- {{FILE}}

test:
    cargo build --bin faithc
    cargo run --bin run_tests -- ./target/debug/faithc ./tests

