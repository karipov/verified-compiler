# Simple Verified Compiler

I'm taking CS1260 (Compilers) with Rob this semester, alongside Formal Proof and Verification. In the initial brainstorming stages of the project, Rob suggested I build a verified compiler using a very simple AST from the very beginning of our class:

```lean
inductive Expr
| Num (n : Nat)
| Add1 (e : Expr)
| Sub1 (e : Expr)
```

## Correctness

The statement of correctness of this verified compiler is roughly the following:

> Given some input program `p`, as an AST, suppose that executing the interpreter on `p` produces a value `v`. If we compile and run `p`, the output (treated as a value) should also be `v`.

To that end, there is the compiler, which takes programs of type `Expr` and translates them into `List Directive` -- assembly instructions. Then, the processor, which has some state and a semantics for interpreting assembly instructions, produces a value. 

Given that our AST is simple enough that we do not have undefined behavior (e.g. adding two booleans), we can formalize the correctness statement as follows:

```lean
∀ prog : Expr, Processor.evalToValue (compile_expr prog) = interpret_expr prog
```

The proof of this statement can be found in `Compare.lean`

## Exploratory work

There are also two incomplete branches (found in brackets with titles below) within this repository that are related to additional exploratory work I've been doing as part of this project. I'm excited to continue this work into the winter! Since this file will likely be seen only in Gradescope, here's a [link to my repository](https://github.com/karipov/verified-compiler/tree/booleans).

### Booleans (`booleans`)

Adding booleans to this AST introduces a number of challenges, including undefined behavior. For example, what should the interpreted result of `Add1 (true)` be? Therefore, the signature for the interpreter needs to change:

``` lean
-- before
def interpret_expr : Expr → Value
-- after
def interpret_expr : Expr → Option Value
```

However, where does this leave us in terms of the compiler, which cannot pattern match and return optional values? The answer is that we must adjust the correctness statement

> Suppose that `p` is an input program, as an AST, and executing the interpreter on `p` produces some value `v`. Then, if we compile and run `p`, the output (treated as a value) should also be `v`.

Essentially, we only consider the correctness when our interpreter produces a value:

```lean
theorem correctness : ∀ prog : Expr,
  (interpret_expr prog).isSome →
  Processor.evalToValue (compile_expr prog) = interpret_expr prog
```

Another difficulty presented by this change is value tagging. In the compiler, to find out how to output the values, each is tagged with a boolean tag. When doing certain operations or presenting the final result, we must untag the values. This presents additional difficulty in writing theorems about how tagging and untagging does not change the final values.

### Stack (`add-two`)

I also thought about extending the AST to support an operation like `(Add 1 2)`. The correct compilation of this operation requires us to use the stack. [This lecture](https://browncs1260.github.io/notes/6) in cs1260 on binary operators goes into more detail.

In Lean4, I modeled the stack as a list, with `push` and `pop` operations. This required extending the processor behavior for these functions, and more. This prove has been difficuilt, but some progress is being made!


## Update (October 2026)

- The project now builds with Lean `v4.34.1` and no longer depends on Mathlib. None of the proofs needed it, so `LoVelib.lean` is gone too, and `lake build` takes a few seconds.
- **`booleans`** is finished. The induction goes through a stronger lemma, `compile_expr_rax`: whenever the interpreter produces a value, the compiled code leaves that value's *tagged encoding* in `rax`. Then `evalToValue_encode` shows that untagging gives the value back. (The helper `smth` is now `n * 2 ^ sh >>> sh = n`; the old `n * sh ^ 2` version wasn't true, e.g. for `n = sh = 1`.)
- **`add-two`** is finished, but it needed a fix first: the `Pop` operand read the top of the stack without removing it, so nested additions read stale values, and `Add (Num 1) (Add (Num 2) (Num 3))` compiled to 7. `Pop` is now a directive that pops into a register (`push rax; ...; pop rcx; add rax, rcx`). The proof generalizes over the starting state (`compile_expr_spec`): from *any* state, the code for `e` leaves its value in `rax` and leaves the stack the way it found it.
- **`extended`** combines both branches and adds `Sub`, `IsZero`, `Lt` and `If`. `If` needs jumps, so the processor runs code with `Processor.run` instead of `List.foldl`. Jumps are relative ("skip the next `n` directives"), and since the language has no loops they only ever go forwards. The main lemma, `compile_expr_spec`, says that running the code for `e` followed by any `rest` is the same as running `rest` from a state with `e`'s encoding in `rax` and the original stack. That's what shows every jump lands where it should.

### Errors, variables and more operators (`extended`)

The correctness theorem no longer needs the `isSome` hypothesis:

```lean
theorem correctness : ∀ prog : Expr,
  Processor.evalToValue (compile prog) = interpret prog
```

On *every* program the compiled code gives exactly what the interpreter gives, errors included. Three changes got it there.

- **Runtime type errors.** Like in cs1260, the compiler emits a tag check before every operation that needs a number or a boolean: `mov r8, rax; and r8, mask; cmp r8, tag`. If the tag doesn't match, the program calls the error handler, a new `Error` directive. Jumps are relative, so there's no `error` label to jump to. Instead each check ends with `je 1; Error`, which jumps over its own call to the handler when the tag matches. `Processor.run` now returns `Option ProcessorState`, and reaching an `Error` gives `none`. The new proof work is `num_tag_check` and `bool_tag_check`: masking off the tag bits and comparing them is true for every value of the right type and false for every value of the wrong type. A number's encoding ends in `0b00`, and both boolean encodings end in `0b11`, so neither check can be fooled. `If` checks its condition too, so `If (Num 0) ...` is an error rather than taking the true branch.
- **`Let` and variables.** The interpreter carries an environment, `List (String × Value)`. The compiler carries a table, `List (String × Nat)`, that maps each variable to a stack slot, plus `depth`, the number of slots already in use (cs1260's `stack_index`). `Let x e body` pushes `e`'s value into slot `depth`, compiles `body` with `x ↦ depth`, and pops the slot afterwards. `Var x` becomes `Load slot`, a new directive that loads a stack slot into `rax`. Slots count up from the bottom of the stack, like `[rbp - 8 * (slot + 1)]`, so the temporaries that binary operators push don't move them. The proof threads an invariant, `Matches`, through the induction: the table and the environment have the same variables, and each variable's slot holds the encoding of its value. An unbound variable is an error in the interpreter, and the compiler emits `Error` for it. That keeps the two in agreement even on `If (Bool true) (Num 1) (Var "x")`, where the unbound variable is never reached.
- **More operators.** `Not`, `Eq`, short-circuiting `And` and `Or`, `IsNum` (`num?`) and `IsBool` (`bool?`). `And` and `Or` jump over `e₂` when `e₁` already decides the answer. `Eq` compares any two values, like in cs1260, which works because different values always have different encodings (`encode_eq`). `IsNum` and `IsBool` run the same tag test as the checks, but put the answer in `rax`. They use cs1260's `zf_to_bool` and `cf_to_bool` helpers, which `IsZero` and `Lt` now use too.

`compile_expr_spec` is now stated with `Runs`. If the interpreter gives an error, the code for `e` ends in an error whatever follows it. Otherwise it falls through to whatever follows, with the value in `rax` and the stack it started with. `Examples.lean` runs a few programs through the compiled code every time the project builds.


## Resources

These have been invaluable as I have worked on this project. I borrowed heavily from Rob's work in our compilers class.

- Rob's cs1260 class compiler in lean4: https://github.com/BrownCS1260/class-compiler-2022/tree/main/lean4/ClassCompiler 
- Simple stack machine verified compiler by jdan: https://github.com/jdan/compiler.lean
- Computerphile youtube video on program correctness: https://www.youtube.com/watch?v=T_IINWzQhow
- More complex verfied compiler by leo okawa ericson: https://uu.diva-portal.org/smash/get/diva2:1613286/FULLTEXT01.pdf

Somewhat unrelated:
- Trustworthy C compiler: https://compcert.org/man/manual001.html
