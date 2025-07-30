# Borrowing from Session Types

This repository contains an implementation of a typechecker and interpreter
for the language from the paper *Borrowing from Session Types*.

The implementation supports all features mentioned in the paper and additionally
supports the following features:

- unrestricted base types `String`, `Int`, and `Bool` with the usual operations;

- unrestricted function types;

- recursive function definitions and recursive session types;

- irrefutable pattern matching in let expressions for products;

- a function that prints to stdout.

Note that the `spawn` expression differs from the paper in that it is
call-by-need, and hence does not require you to wrap its subexpression in a
lambda, e.g. instead of `spawn (λ(). e)` you can directly write `spawn e`.

## Installation

### Docker

1.  Build the image via

    ```bash
    docker-compose build
    ```

2.  Run the image via

    ```bash
    docker-compose run bsti
    ```

    This drops you into an interactive bash shell, where the compiled
    interpreter `bsti` is already on the `PATH`.

3.  Typecheck and interpret a program via e.g.

    ```bash
    bsti examples/positive/example-simple.bgv
    ```

    The current host directory is mounted into the current guest directory, so
    it is possible to change or add examples on the host without having to
    rebuild the image.

### From Source

Install a recent version of stable rust. See the following URL for instructions:

https://www.rust-lang.org/tools/install

The following command will compile the project and its dependencies (if necessary),
and then typecheck and run the file `SOURCE_FILE`:

```bash
cargo run -- SOURCE_FILE
```

## Syntax

The following grammar describes the complete, concrete syntax supported by the interpreter.
For readability, operator precedence, associativity and whitespace are omitted.

```
Multiplicities
m ::= 'u' | 'unr'                   (unrestricted)
    | 'p' | 'lin'                   (linear/"parallel")
    | 'l' | 'left'                  (left ordered)
    | 'r' | 'right'                 (right ordered)

Effects
E ::= '0'                           (pure)
    | '1'                           (impure)

Types
t ::= t '-[' m ';'? E ']->' t       (function type)
    | t '*[' m ']' t                (product type)
    | '<' (l ':' t ',')* '>'        (variant type)
    | 'Chan'? s                     (session type)
    | 'Unit'                        (unit type)
    | 'Int'                         (64bit signed integer type)
    | 'Bool'                        (boolean t type)
    | 'String'                      (unicode string type)

Session Types
s ::=  '!' t '.' so                 (sending session type)
     | '?' t '.' so                 (receiving session type)
     | '+{' (l ':' s ',')* '}'      (internal choice type)
     | '&{' (l ':' s ',')* '}'      (external choice type)
     | 'Close'                      (sending end of protocol of owned session)
     | 'Wait'                       (receiving end of protocol of owned session)
     | 'Return'                     (end of protocol of borrowed session)
     | 'mu' x '.' s                 (recursive session type)
     | x                            (session variable)

Expressions
e ::= x                             (variable)
    | '\' x '.' e                   (lambda abstraction)
    | e e                           (unr/lin/right function application)
    | e '|>' e                      (left function application with flipped arguments)

    | 'let' x '=' e 'in' e          (let expression)
    | e ';' e                       (sequencing)

    | '(' e ',' e ')'               (pairs)
    | 'let' x ',' x '=' e 'in' e    (product elimination)

    | 'inj' l e                     (variant introduction)
    | 'case' e '{'                  (variant elimination)
        (l x '->' '{' e '}')*
      '}'

    | 'let' x ':' t '\n'
            x p+ '=' e 'in' e       (let expression for recursive function
                                     with irrefutable pattern matching clauses)

    | 'fork' e                      (thread spawning)
    | 'new' s                       (channel allocation)
    | 'send' e1 e2                  (channel send operation)
    | 'recv' e                      (channel receive operation)
    | 'branch' e                    (external choice operation)
    | 'select' l e                  (internal choice operation)
    | 'drop' e                      (elimination of borrowed channels)
    | 'close' e                     (elimination of owned channels)
    | 'wait' e                      (elimination of owned channels)
    | '&' x                         (borrow)

    | 'true' | 'false'              (boolean introduction)
    | 'if' e 'then' e 'else' e      (boolean elimination)
    | e '&&' e                      (boolean conjunction)
    | e '||' e                      (boolean disjunction)
    | '!' e                         (boolean negation)

    | 'unit'                        (unit introduction)

    | <str>                         (string literals)
    | e '+' e                       (string concatenation)
    | 'str' e                       (conversion to string)
    | 'print' e                     (printing to stdout)

    | <int>                         (integer literals)
    | '-' e                         (integer negation)
    | e '+' e                       (integer addition)
    | e '-' e                       (integer subtraction)
    | e '*' e                       (integer multiplication)
    | e '/' e                       (integer division)

    | e '<' e                       (comparison)
    | e '<=' e                      (comparison)
    | e '>' e                       (comparison)
    | e '>=' e                      (comparison)
    | e '==' e                      (equality)
    | e '!=' e                      (inequality)

    | e ':' t                       (type annotation)
    
Variables
x ::= [a-zA-Z_]+[a-zA-Z0-9_]*

Labels
l ::= [a-zA-Z_]+[a-zA-Z0-9_]*

Integer Literals
<int> ::= '-'? [0-9]+

String Literals
<str> ::= '"' [^"]* '"'             (strings like "foo")
        | '\'' [^"]* '\''           (strings like 'foo')
        | '\'\'\'' [^"]* '\'\'\''   (strings like '''foo''')

Patterns
p ::= x                             (variable pattern)
    | '(' p1 ',' p2 ')'             (pair pattern)
    
Program
P ::= e                             (main expression)
```

We also provide unicode alternatives for certain tokens:

- A lambda `\x. e` can also be written as `λx. e`

- A function type `t1 -[ m E ]-> t2` can also be written as `t1 –[ m E ]→ t2`

- An unordered product type `t1 *[ p ] t2` can also be written as `t1 ⊗ t2`

- A left-ordered product type `t1 *[ l ] t2` can also be written as `t1 ⊙ t2`

- A recursive session type `mu x. s` can also be written as `µ x. s`

Comments are started with a `#` and range until the end of the line.

## Examples

The following shows the obligatory math server example:

```agda
let 
  server : ?Int.?Int.!Int.Wait -[ u 1 ]→ Unit
  server c =
    let x = recv &c in
    let y = recv &c in
    send (x + y) &c;
    wait c
in

let
  client : !Int.!Int.?Int.Close -[ u 1 ]→ Unit
  client c =
    send 1 &c;
    send 2 &c;
    print (recv &c);
    close c
in

let c1, c2 = new !Int.!Int.?Int.Close in
fork (server c2);
client c1
```

This example can also be written without the syntactic sugar for Haskell-style
function definitions, i.e. as simple `let`-expressions, where the body is
a lambda wrapped in a type annotation expression `(\c. …) : t`:

```agda
let 
  server = \c.
    let x = recv &c in
    let y = recv &c in
    send (x + y) &c;
    wait c
  : ?Int.?Int.!Int.Wait -[ u 1 ]→ Unit
in

let
  client = \c.
    send 1 &c;
    send 2 &c;
    print (recv &c);
    close c
  : !Int.!Int.?Int.Close -[ u 1 ]→ Unit
in

let c1, c2 = new !Int.!Int.?Int.Close in
fork (server c2);
client c1
```

Further examples, including the examples from the paper can be found in the
`examples` subdirectory.
