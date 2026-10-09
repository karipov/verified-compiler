import VerifiedCompiler.Process
import VerifiedCompiler.Compile
import VerifiedCompiler.Interpret

open Value Expr Directive Operand Register

def Processor.evalToValue (ds : List Directive) : Value :=
  match Processor.eval ds with
  | Sum.inl n => Integer n
  | Sum.inr b => Boolean b

theorem shl_shr (n sh : Nat) : n <<< sh >>> sh = n :=
  Nat.shiftLeft_shiftRight n sh

-- (this used to say `n * sh ^ 2`, which isn't true: n = 1, sh = 1 gives 1 >>> 1 = 0)
theorem smth (n sh : Nat) : (n * 2 ^ sh) >>> sh = n :=
  by
    rw [← Nat.shiftLeft_eq, shl_shr]

theorem land_helper (n : Nat) : n * 2 ^ 2 &&& 3 = 0 :=
  by
    have hmod := Nat.and_two_pow_sub_one_eq_mod (n * 2 ^ 2) 2
    simp_all

-- the bits that end up in rax for each value: numbers are shifted left past a 0b00 tag,
-- booleans are shifted left past a 0b0011111 tag
def encode : Value → Nat
| Integer n => n <<< num_shift
| Boolean b => (if b then 1 else 0) <<< bool_shift ||| bool_tag

theorem compile_bool (b : Bool) :
  compile_expr (Expr.Bool b) = [Mov (Reg Rax, Imm (encode (Boolean b)))] :=
  by
    cases b <;> rfl

-- untagging an encoded value gives back the value
theorem evalToValue_encode (ds : List Directive) (v : Value)
  (h : (Processor.evalToState ds).rax = encode v) :
  Processor.evalToValue ds = v :=
  by
    cases v with
    | Integer n =>
      simp only [Processor.evalToValue, Processor.eval, h, encode, num_shift, num_mask, num_tag]
      rw [Nat.shiftLeft_eq, land_helper, smth]
      rfl
    | Boolean b =>
      cases b <;> simp [Processor.evalToValue, Processor.eval, h, encode, num_mask, num_tag,
        bool_shift, bool_mask, bool_tag]

-- `correctness` only tells us the *untagged* result of the code for `e`, but to know what
-- `Add1 e` and `Sub1 e` compute we need the actual bits in rax. so the induction is done on
-- this stronger statement: whenever the interpreter produces a value, the compiled code
-- leaves exactly that value's encoding in rax.
theorem compile_expr_rax :
  ∀ (prog : Expr) (v : Value),
    interpret_expr prog = some v → (Processor.evalToState (compile_expr prog)).rax = encode v
  | Expr.Num n, v, h =>
    by
      simp only [interpret_expr, Option.some.injEq] at h
      subst h
      simp [compile_expr, encode, Processor.evalToState, processDirective,
        ProcessorState.setReg, ProcessorState.opVal]

  | Expr.Bool b, v, h =>
    by
      simp only [interpret_expr, Option.some.injEq] at h
      subst h
      simp [compile_bool, Processor.evalToState, processDirective, ProcessorState.setReg,
        ProcessorState.opVal]

  | Expr.Sub1 e, v, h =>
    by
      -- `Sub1 e` only has a value if `e` evaluates to some integer i
      simp only [interpret_expr] at h
      split at h
      case h_1 i he =>
        simp only [Option.some.injEq] at h
        subst h
        have ih := compile_expr_rax e (Integer i) he
        simp only [compile_expr, Processor.evalToState, List.foldl_append] at *
        simp [processDirective, ProcessorState.setReg, ProcessorState.regVal,
          ProcessorState.opVal, ih, encode, num_shift, Nat.shiftLeft_eq, Nat.sub_mul]
      case h_2 => contradiction

  | Expr.Add1 e, v, h =>
    by
      -- `Add1 e` only has a value if `e` evaluates to some integer i
      simp only [interpret_expr] at h
      split at h
      case h_1 i he =>
        simp only [Option.some.injEq] at h
        subst h
        have ih := compile_expr_rax e (Integer i) he
        simp only [compile_expr, Processor.evalToState, List.foldl_append] at *
        simp [processDirective, ProcessorState.setReg, ProcessorState.regVal,
          ProcessorState.opVal, ih, encode, num_shift, Nat.shiftLeft_eq, Nat.add_mul]
      case h_2 => contradiction

-- the compiler will produce the same value when the interpreter produces a some
theorem correctness : ∀ prog : Expr,
  (interpret_expr prog).isSome →
  Processor.evalToValue (compile_expr prog) = interpret_expr prog :=
  by
    intro prog hsome
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hsome
    rw [hv, evalToValue_encode _ v (compile_expr_rax prog v hv)]
