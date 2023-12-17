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


## Resources

These have been invaluable as I have worked on this project. I borrowed heavily from Rob's work in our compilers class.

- Rob's cs1260 class compiler in lean4: https://github.com/BrownCS1260/class-compiler-2022/tree/main/lean4/ClassCompiler 
- Simple stack machine verified compiler by jdan: https://github.com/jdan/compiler.lean
- Computerphile youtube video on program correctness: https://www.youtube.com/watch?v=T_IINWzQhow
- More complex verfied compiler by leo okawa ericson: https://uu.diva-portal.org/smash/get/diva2:1613286/FULLTEXT01.pdf

Somewhat unrelated:
- Trustworthy C compiler: https://compcert.org/man/manual001.html
