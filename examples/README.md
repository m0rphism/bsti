# Examples

This directory contains example programs in our language.

## Structure

The examples are located in two subdirectories:

1.  In `positive/` are examples of well-typed programs.

2.  In `negative/` are examples of ill-typed programs.

The files in these subdirectories are named as followed:

- Files starting with `paper-` are examples taken verbatim from the paper.

- Files starting with `math-server-` show how to incrementally build a math-server.

- Files starting with `other` are extra examples.

## Running Examples

The examples can be run either manually, e.g.

```bash
cargo run -- examples/positive/example-branching.bgv
```

or for an already installed interpreter:
```bash
bsti examples/positive/example-branching.bgv
```

The examples can also be run all at once via

```bash
cargo test
```

The `cargo test` command runs a unit test that ensures that each `.bgv` file in
the `positive/` directory typechecks, and that each `.bgv` file in the
`negative/` directory does not.
