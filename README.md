# Law and Order for Typestate with Borrowing

Implementation of a typechecker and interpreter for the language from the paper
*Law and Order for Typestate with Borrowing*.

The only partial monoid supported so far are regular expressions.

## Dependencies

- Rust ([Installation Tutorial](https://www.rust-lang.org/tools/install))

## Usage

The following command will compile the project and its dependencies (if necessary) and
typecheck and run the file `SOURCE_FILE`:

```bash
cargo run -- SOURCE_FILE
```

## Syntax

```
Multiplicities
m ::= 'u' | 'unr'      (unrestricted)
    | 'p' | 'lin'      (linear/"parallel")
    | 'l' | 'left'     (left ordered)
    | 'r' | 'right'    (right ordered)

Effects
E ::= '0'   (pure)
    | '1'   (impure)

Types
t ::= t '-[' m ';'? E ']->' t  (function type)
    | t '*[' m ']' t           (product type)
    | 'Unit'                   (unit type)
    | r                        (resource type)

Expressions
e ::= e ':' t                       (type annotation)
    | '\' ('[' m ']')? x '.' e      (lambda with optional multiplicity annotation)
    | 'let' x ',' x '=' e 'in' e    (product elimination)
    | 'let' x '=' e 'in' e          (let expression)
    | 'let' x ':' t '\n'
            x p+ '=' e 'in' e       (let expression for pattern matching function)
    | e ';' e                       (sequencing)
    | 'new' r                       (resource allocation)
    | '!' r e                       (resource operation)
    | 'split' r e                   (resource splitting)
    | 'drop' e                      (resource deallocation)
    | e e                           (function application)
    | '(' e ',' ('[' m ']')? e ')'  (pair with optional multiplicity annotation)
    | 'unit'                        (unit value)
    | x                             (variable)
    
Variables
x ::= [a-zA-Z_]+[a-zA-Z0-9_]*

Patterns
p ::= x                  (variable pattern)
    | '(' p1 ',' p2 ')'  (pair pattern)
    
Program
P ::= e    (main expression)
    | D P  (declaration)

Resources (Regular Expressions)
r ::= '{' '}'     (short form of epsilon regex)
    | '{' r_ '}'  (arbitrary regex)
    
r_ ::= ϵ          (epsilon regex)
     | ∅          (empty regex)
     | [a-zA-Z]   (atom)
     | r_ r_      (sequence)
     | r_ '|' r_  (disjunction)
     | r_ '*'     (Kleene closure)
```

We also provide unicode alternatives for certain tokens:
- A lambda `\x. e` can also be written as `λx. e`
- A function type `t1 -[ m E ]-> t2` can also be written as `t1 –[ m E ]→ t2`
- An unordered product type `t1 *[ p ] t2` can also be written as `t1 ⊗ t2`
- A left-ordered product type `t1 *[ l ] t2` can also be written as `t1 ⊙ t2`

Comments are started with a `#` and range until the end of the line.

## Example

```
# Function that does operation 'x' and then drops the resource.
let f = λc. drop (!{x} c) 
      : {x} –[ u 1 ]→ Unit in
let r = new {xy} in
let r1, r2 = split {x} r in
f r1;
drop (!{y} r2)
```

or with declarations:

```
# Function that does operation 'x' and then drops the resource.
let
  f : {x} –[ u 1 ]→ Unit
  f c = drop (!{x} c)
in

let r = new {xy} in
let r1, r2 = split {x} r in
f r1;
drop (!{y} r2)
```
