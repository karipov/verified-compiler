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

### Where it is now (`extended`)

The language now has booleans, arithmetic and comparisons, `if`, `let`, pairs, and top-level functions with recursion. Programs are written as s-expressions, in the same style as cs1260:

```lisp
; lists are nested pairs ending in false
(define (range n)
  (if (zero? n) false (pair n (range (sub1 n)))))

(define (sum l)
  (if (pair? l) (+ (left l) (sum (right l))) 0))

(sum (range 1000))
```

The forms are `add1`, `sub1`, `+`, `-`, `zero?`, `<`, `if`, `not`, `=`, `and`, `or`, `num?`, `bool?`, `let`, `pair`, `left`, `right`, `pair?`, `define` and function calls. Numbers are natural numbers, so subtraction stops at 0.

#### The theorem

```lean
theorem correctness (prog : Program) (fuel : Nat) :
  Processor.evalToValue fuel (compile prog) = interpret fuel prog
```

There are no hypotheses. Both sides give an `Outcome`: a value, an `error`, or a `timeout`. An error is a type error like `(add1 true)`, an unbound variable, or calling a function that doesn't exist or with the wrong number of arguments. Recursion means a program can run forever. So the interpreter and the processor both get *fuel*, and both use up one unit on every function call. Since the two sides agree for every amount of fuel, they also agree on which programs run forever: those are the ones that time out whatever the fuel.

#### How the compiler works

- **Values** are tagged 64-bit words, like in cs1260. Numbers are shifted left past a `0b00` tag, booleans past `0b0011111`, and a pair is a pointer to two words on the heap, tagged `0b010`.
- **Type checks.** Before each operation that needs a number, boolean or pair, the compiler emits `mov r8, rax; and r8, mask; cmp r8, tag`, and calls the error handler (a new `Error` directive) if the tag doesn't match. Jumps are relative, so there's no shared `error` label to jump to; each check ends with `je 1; Error`, which jumps over its own call to the handler. `if`, `and` and `or` check their conditions, so `(if 0 1 2)` is an error. `=` compares numbers and booleans. On pairs it's an error, since comparing them would mean comparing pointers, which the interpreter has no notion of.
- **Variables** live in the current stack frame. The compiler keeps a table from each variable to its slot and `depth`, the size of the frame (cs1260's `stack_index`). `Var x` becomes `Load k`, which is `mov rax, [rsp + 8 * k]` with `k = depth - 1 - slot`.
- **Pairs** go on the heap. `r15` is the heap pointer: the two halves are stored at `[r15]` and `[r15 + 8]`, the tagged pointer goes in `rax`, and `r15` moves up 16 bytes. There's no garbage collector.
- **Functions.** A call pushes the arguments, runs `Call f`, then drops the arguments again. Inside the function, the arguments and the return address make up the bottom of its frame. `Call` and `Ret` are the only way control goes backwards, so `Processor.run` needs fuel only for `Call`.
- **Flags.** On a real processor `add`, `sub` and `and` change the flags too. In the model they wipe them, and a conditional jump on a wiped flag is an error. So the proof also shows the compiled code never relies on a flag that something else changed in the meantime.

#### How the proof works

`compile_expr_spec` is stated with `Spec`, which says what running some code does when the program should end up with a given outcome. On an error or a timeout, that's what happens, whatever code comes after. On a value, the code falls through to whatever comes after it, in a state where the postcondition holds. Every interpreter case is written with `do`, and `Spec.bind` turns each `>>=` into "run this code, then that code". So each case is a short chain of combinators: `Spec.bind` for subexpressions, `Spec.step` and `Spec.jump` for single directives, `Spec.ensure_num` and friends for the type checks, and `Spec.call` for calls.

Three invariants carry the rest:

- `Encodes mem hp v w`: the word `w` stores the value `v` in the heap `mem`, with everything it points to below `hp`. A pair's halves are stored before the pair is, so they sit below its address. That keeps `decode`, which reads values back out, obviously terminating. `Encodes.mono` shows a stored value stays valid as the heap grows, and `num_check`, `bool_check` and `pair_check` show the bitwise tag tests accept exactly the values of the right type.
- `Matches`: the compiler's table and the interpreter's environment have the same variables, and each variable's slot in the frame holds its value. `Matches.entry` sets this up for a function's parameters.
- Fuel: `compile_expr_spec` holds at fuel `n` as long as calls work with any fuel below `n`, since a call runs the function with one less. `calls_ok` ties the knot by strong induction on the fuel.

#### Running it on a real machine

`Emit.lean` prints the compiled code as x86-64 assembly for nasm, and `runtime/runtime.c` sets up the heap, calls it, and prints the answer.

```sh
lake exe vc run tests/fact.lisp      # interpret it: 3628800
lake exe vc model tests/fact.lisp    # run the compiled code on the processor in Process.lean
lake exe vc asm tests/fact.lisp      # print the assembly
tests/run.sh                         # build every program in tests/ and compare with the interpreter
tests/run.sh --random 500            # the same, for 500 random programs from `vc gen`
```

`tests/run.sh` needs nasm and a C compiler. It builds each program into a real binary and checks that the binary prints the same thing, with the same exit code, as the interpreter.

The proof covers everything up to the processor in `Process.lean`. The assembly printer and the C runtime aren't verified. They're a direct translation of that processor, and the tests are there to check the translation. There are also places where real hardware has limits that the model doesn't:

- Words are 64 bits, so numbers need to stay below 2^62, and the printer refuses literals that don't fit.
- The heap is 128 MiB and the stack is whatever the system gives. A program that runs forever overflows the stack instead of timing out.
- The model's heap starts at address 0, and the real one starts wherever the runtime allocated it. That doesn't change any answers: pointers are only ever followed or tag-checked, and the real heap is 16-byte aligned.

## Resources

These have been invaluable as I have worked on this project. I borrowed heavily from Rob's work in our compilers class.

- Rob's cs1260 class compiler in lean4: https://github.com/BrownCS1260/class-compiler-2022/tree/main/lean4/ClassCompiler 
- Simple stack machine verified compiler by jdan: https://github.com/jdan/compiler.lean
- Computerphile youtube video on program correctness: https://www.youtube.com/watch?v=T_IINWzQhow
- More complex verfied compiler by leo okawa ericson: https://uu.diva-portal.org/smash/get/diva2:1613286/FULLTEXT01.pdf

Somewhat unrelated:
- Trustworthy C compiler: https://compcert.org/man/manual001.html
