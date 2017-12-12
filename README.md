**`ppx_stage`** adds support for staged metaprogramming to OCaml,
allowing type-safe generation, splicing and evaluation of bits of
OCaml source code. `ppx_stage` is heavily inspired by
[MetaOCaml](http://okmij.org/ftp/ML/MetaOCaml.html), and can run many
of the same programs (albeit with a slightly different syntax for
staging). See [test/strymonas.ml](test/strymonas.ml) for a large example.

Install it with:

    opam pin add ppx_stage git://github.com/stedolan/ppx_stage.git
    
After it's installed, you can load it into a standard OCaml toplevel:

    #use "topfind";;
    #require "ppx_stage.ppx";;

`ppx_stage` doesn't need a special compiler switch - it's compatible
with any recent version of OCaml.

Once it's loaded, you'll be able to use the `[%code ...]` syntax to
construct program fragments:

    # let greeting = [%code print_string "Hello!\n"];;
    val greeting : unit Ppx_stage.code = {Ppx_stage.compute = <fun>; source = <fun>}

The default output's pretty ugly, so install a better printer before
going any further:

    # #install_printer Ppx_stage.print;;
    # let greeting = [%code print_string "Hello!\n"];;
    val greeting : unit Ppx_stage.code = print_string "Hello!"

Note that it hasn't printed `Hello!` yet: greeting is a value of type
`unit Ppx_stage.code`, which means it's the source code of a program
which, when run, returns `unit`. We can run the program with
`Ppx_stage.run`, and then we'll see the message:

    # Ppx_stage.run greeting;;
    Hello!
    - : unit = ()

You can think of `[%code ...]` as being like `fun () -> ...`,
producing a value which represents a block of code that has not yet
been run. There are two important differences: first, we can access the
source code of programs built with `[%code ...]` (using `Ppx_stage.print`
to pretty-print it, or using `Ppx_stage.to_parsetree` to get the
raw syntax tree). Secondly, we can splice multiple blocks of code
together using *escapes*.


## Splicing and escapes

Inside `[%code ...]` blocks, the syntax `[%e ...]` lets you splice in
a piece of code into the middle of a template. For example:

    # let two = [%code 2];;
    val two : int Ppx_stage.code = 2
    # let three = [%code 1 + [%e two]];;
    val three : int Ppx_stage.code = 1 + 2

The escapes `[%e ...]` (sometimes known as "antiquotations") take a
value of type `'a code`, and splice it into a surrounding piece of
code as an `'a`.

The expression in the `[%e ...]` is run once, while the program is
being generated, and doesn't form part of the generated code. This
will make more sense with an example:

    # let random_number_code () = Ppx_stage.Lift.int (Random.int 100);;

Here, `random_number_code ()` produces source code for a random
number, by using `Ppx_stage.Lift.int` to turn an `int` into an `int
code` (Unlike MetaOCaml, `ppx_stage` does not automatically let `'a`
be turned into `'a code` - values from the host program have to be
explicitly lifted if they are used in the generated program).

We can use escapes to splice `random_number_code ()` into a bigger
program:

    # let p = [%code 2 * [%e random_number_code ()]];;
    val p : int Ppx_stage.code = 2 * 17

When `[%code 2 * [%e random_number_code ()]]` was evaluated, OCaml
first evaluated `random_number_code ()` (which this time returned
`[%code 17]`), and then spliced that into `[%code 2 * [%e ...]]`
giving `[%code 2 * 17]`. The call to `random_number_code ()` isn't
part of `p`: the source code of `p` is the program `2 * 17`, and every
time it runs it produces the same value:

    # Ppx_stage.run p;;
    - : int = 34
    # Ppx_stage.run p;;
    - : int = 34

We can generate a new program by rerunning `random_number_code ()`:

    # let q = [%code 2 * [%e random_number_code ()]];;
    val q : int Ppx_stage.code = 2 * 85

This second call to `random_number_code ()` returned a different
value, but again `q` returns the same value every time it is run:

    # Ppx_stage.run q;;
    - : int = 170
    # Ppx_stage.run q;;
    - : int = 170


## Binding

The scopes of variables in stage programs extend into nested escapes
and `[%code ...]` blocks, which is surprisingly useful. Below is a
staged version of `List.map`:

``` ocaml
let map f = [%code
  let rec go = function
    | [] -> []
    | x :: xs -> [%e f [%code x]] :: go xs in
  go]
```

The tricky part here is `f [%code x]`: the `x` being passed to `f`
refers to the `x` that was bound by `x :: xs` in the enclosing `[%code
...]` block.

The type of this function is worth a close look:

``` ocaml
val map :
  ('a Ppx_stage.code -> 'b Ppx_stage.code) ->
  ('a list -> 'b list) Ppx_stage.code = <fun>
```

`map` takes a function from `'a code` to `'b code`, and returns code
for a function from `'a list` to `'b list`. So, the `f` that we pass
to `map` is given code for the current element of the list, and
returns code for its replacement. We can write such an `f` using splicing:

``` ocaml
let plus1 x = [%code [%e x] + 1]
```

Then, `map plus1` splices `plus1` into `go`, giving this code:

``` ocaml
# map plus1;;
- : (int list -> int list) Ppx_stage.code =
let rec go = function | [] -> [] | x::xs -> (x + 1) :: (go xs)  in go
```

This `map` isn't the standard `List.map` function - instead, it's a
template that produces a specialised `map` function, when given the
code for processing each element.

This style can be used to write efficient libraries that generate
optimised code. For a detailed example, read the paper [Stream Fusion,
to Completeness](https://strymonas.github.io/) (by Oleg Kiselyov,
Aggelos Biboudis, Nick Palladinos and Yannis Smaragdakis), or play
with [their MetaOCaml
library](https://github.com/strymonas/staged-streams.ocaml) or [a port
of it to `ppx_stage`](test/strymonas.ml).

Code written in this style tends to involve writing many functions
like `plus1`, which map code for a value to code for a result. To make
them a bit less syntactically noisy, `ppx_stage` supports `fun%staged`
as syntactic sugar for the combination of `[%code ...]` and `[%e
...]`, allowing:

    map (fun%staged x -> x + 1)


## Typing and hygiene

So far, most of what's been described here could be accomplished with
horrible string concatenation trickery. Two aspects of `ppx_stage`
require a bit more, though: typing and hygiene.

First, all `[%code ...]` and `[%e ...]` blocks are statically typed: a
value of type `'a code` is the source code of a program producing
`'a`, and if the original program passes the OCaml typechecker, then
it cannot generate ill-typed code. Instead of modifying the
typechecker, this is accomplished by translating each `[%code ...]`
block into a pair of expressions: the first is the body (the `...`),
unmodified except for `[%e ...]` escapes, and the second is code that
produces a syntax tree for the body given syntax trees for the
escapes. This translation is untyped, but by ensuring both half of the
pair represent the same code, we know that if the first passes the
OCaml typechecker then the second generates type-correct code.

The second issue is hygiene: under certain circumstances, `ppx_stage`
may need to rename variables to prevent undesired shadowing. For
instance, suppose we have a function that produces constant functions
(that is, functions that ignore their argument):

``` ocaml
let const v = [%code fun x -> [%e v]]
```

Now suppose we use this as `[%code fun x -> [%e const [%code x]]]`. If
we were to just splice strings together, we might end up with:

    fun x -> fun x -> x

which is wrong: the variable `x` at the end should refer to the outer
binder, not the one introduced by `const`. Instead, `ppx_stage`
generates this code:

    fun x  -> let x''1 = x  in fun x  -> x''1

which introduces an alias `x''1` for `x` so that it can be referred to
even when `x` is shadowed.

## Polymorphism

Because of how `ppx_stage` implements staging, some of the usual
difficulties in staging polymorphic functions are avoided. Code like
this works as expected:

``` ocaml
# [%code let id x = x in (id 1, id "foo")];;
- : (int * string) Ppx_stage.code =
let id x = x  in ((id 1), (id "foo"))
```

There are two subtle restrictions on polymorphism.  First, variables bound in
staged programs have monomorphic types in nested `[%code ...]`
expressions. For instance, this code won't compile:

``` ocaml
# fun f -> [%code let id x = x in [%e f [%code (id 1, id "foo")]]];;
Error: This expression has type string but an expression was expected of type
         int
```

The function `id` is polymorphic, but the use of `id` in the nested
`[%code ...]` block must be monomorphic.

Second, since splices are translated to applications, code generated
from splices is subject to the (relaxed) value restriction.  For
example, the following code is given a non-polymorphic type:

```ocaml
# [%code fun x -> [%e [%code x]]];;
- : ('_a -> '_a) Ppx_stage.code = fun x  -> x
```


## Modules and functors

*(Support for staged modules and functors is even more experimental
than the rest of `ppx_stage`. Expect breaking changes.)*

By default, modules definitions are not in scope in `[%code ...]`
blocks and do not appear in staged programs, so the following gives a
type error:

``` ocaml
module M : sig
  val x : int
end = struct
  let x = 42
end
let foo y = [%code M.x + [%e y]] (* Error: M.x not in scope *)
```

To make the definition of `M.x` visible in the staged program, we need
to annotate the module binding, its signature and its definition:

``` ocaml
module%code M : sig[@code]
  val x : int
end = struct[@code]
  let x = 42
end
let foo y = [%code M.x + [%e y]] (* works *)
```

When we print e.g. `foo [%code 10]`, the output will include any
staged module definitions that the result depends on:

``` ocaml
module M'1 = struct let x = 42  end
let _ = M'1.x + 10 
```

Here, the module `M` has been renamed to `M'1`. In this example, the
renaming is not terribly helpful, but in general the renaming is
necessary to prevent multiple staged modules with the same name being
confused.

For programs using modules to group and namespace related definitions,
staging just means adding `%code` to module bindings and `[@code]` to
structures (and signatures, if present). To write more advanced staged
programs (e.g. using functors), you need to understand what the
separate annotations do.

A *staged module* is a module annotated with `[@code]`, which
instructs `ppx_stage` to record the source code as well as the
contents of the module, just like `[%code ...]` does for
expressions. Staged modules have staged signatures, which are also
written with [@code], so we can write:

```
module Staged : sig[@code]
  val x : int
end = struct[@code]
  let x = 42
end
```

We get a type error if only one of the `[@code]` annotations is
present: staged signatures are different from their unstaged
counterparts.

A staged module is not automatically made available to staged
expressions using `[%code ...]`. Instead, it must be explicitly
*exported* using the syntax `module%code`:

``` ocaml
module%code M = Staged
```

Separating the construction and export of a staged module like this is
important for writing code using functors, when a functor might export
a staged module passed as a parameter. For instance:

``` ocaml
module F (A : sig[@code] val x : int end) = struct
  module%code A = A
  let bigger = [%code A.x + 1]
end
module M = F (struct[@code] let x = 42 end)
```

Note that it is necessary to explicitly export `A` using
`module%code`: functor arguments are not automatically exported, even
if they have staged signatures.

Printing `M.bigger` produces the following output:

``` ocaml
module A'1 = struct let x = 42  end
let _ = A'1.x + 1
```

As well as definitions, functor applications can be staged with
`[@code]`. For instance, this functor accepts a staged module of
signature `Map.OrderedType` and builds a map with that key type:

``` ocaml
module MkMap (Key : Map.OrderedType[@code]) = struct
  module%code Key = Key
  module%code KMap = Map.Make (Key) [@code]
  let singleton k v = [%code KMap.singleton [%e k] [%e v]]
end
module StringMap =
  MkMap (struct[@code] type t = string let compare = compare end)
```

Printing `StringMap.singleton [%code "hello"] [%code 5]` gives:

``` ocaml
module Key'1 = struct type t = string
                      let compare = compare  end
module KMap'1 = (Map.Make)(Key'1)
let _ = KMap'1.singleton "hello" 5 
```


