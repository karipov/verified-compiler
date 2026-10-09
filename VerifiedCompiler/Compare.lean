import VerifiedCompiler.Process
import VerifiedCompiler.Compile
import VerifiedCompiler.Interpret

open Value Expr Directive Operand Register

def Processor.evalToValue (ds : List Directive) : Value :=
  match Processor.eval ds with
  | Sum.inl n => Integer n
  | Sum.inr b => Boolean b


/- ## Running code -/

@[simp] theorem Processor.run_nil (st : ProcessorState) : Processor.run st [] = st :=
  by
    rw [Processor.run]

@[simp] theorem Processor.run_cons (st : ProcessorState) (d : Directive) (rest : List Directive) :
  Processor.run st (d :: rest) = Processor.run (processDirective st d) (rest.drop (st.skip d)) :=
  by
    rw [Processor.run]

@[simp] theorem processDirective_jmp (st : ProcessorState) (n : Nat) :
  processDirective st (Jmp n) = st := rfl

@[simp] theorem processDirective_je (st : ProcessorState) (n : Nat) :
  processDirective st (Je n) = st := rfl

@[simp] theorem processDirective_jb (st : ProcessorState) (n : Nat) :
  processDirective st (Jb n) = st := rfl

-- `Mov` doesn't touch the flags, so a conditional jump can come after it
@[simp] theorem processDirective_mov_zf (st : ProcessorState) (r : Register) (o : Operand) :
  (processDirective st (Mov (Reg r, o))).zf = st.zf :=
  by
    cases r <;> rfl

@[simp] theorem processDirective_mov_cf (st : ProcessorState) (r : Register) (o : Operand) :
  (processDirective st (Mov (Reg r, o))).cf = st.cf :=
  by
    cases r <;> rfl


/- ## Tagging -/

theorem shl_shr (n sh : Nat) : n <<< sh >>> sh = n :=
  Nat.shiftLeft_shiftRight n sh

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
| Boolean b => if b then true_val else false_val

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
        bool_shift, bool_mask, bool_tag, true_val, false_val]


/- ## Correctness -/

-- the compiled code for a subexpression is always followed by more code, and with jumps
-- around we need to know that control actually makes it to that code. so the induction is
-- done on this statement: whenever the interpreter produces a value `v`, running the code
-- for `prog` and then `rest` is the same as running `rest` from some state `st'` that has
-- `v`'s encoding in rax and the same stack we started with.
theorem compile_expr_spec :
  ∀ (prog : Expr) (v : Value) (st : ProcessorState),
    interpret_expr prog = some v →
    ∃ st', (∀ rest, Processor.run st (compile_expr prog ++ rest) = Processor.run st' rest) ∧
      st'.rax = encode v ∧ st'.stack = st.stack
  | Expr.Num n, v, st, h =>
    by
      simp only [interpret_expr, Option.some.injEq] at h
      subst h
      refine ⟨processDirective st (Mov (Reg Rax, Imm (n <<< num_shift))), ?_, ?_, ?_⟩
      · intro rest
        simp [compile_expr, ProcessorState.skip]
      · simp [processDirective, ProcessorState.setReg, ProcessorState.opVal, encode]
      · simp [processDirective, ProcessorState.setReg]

  | Expr.Bool b, v, st, h =>
    by
      simp only [interpret_expr, Option.some.injEq] at h
      subst h
      refine ⟨processDirective st (Mov (Reg Rax, Imm (encode (Boolean b)))), ?_, ?_, ?_⟩
      · intro rest
        cases b <;> simp [compile_expr, encode, ProcessorState.skip]
      · simp [processDirective, ProcessorState.setReg, ProcessorState.opVal]
      · simp [processDirective, ProcessorState.setReg]

  | Expr.Sub1 e, v, st, h =>
    by
      simp only [interpret_expr] at h
      split at h
      case h_1 i he =>
        simp only [Option.some.injEq] at h
        subst h
        obtain ⟨st₁, hrun₁, hrax₁, hstack₁⟩ := compile_expr_spec e (Integer i) st he
        refine ⟨processDirective st₁ (Directive.Sub (Reg Rax, Imm (1 <<< num_shift))), ?_, ?_, ?_⟩
        · intro rest
          simp [compile_expr, hrun₁, ProcessorState.skip]
        · simp [processDirective, ProcessorState.setReg, ProcessorState.regVal,
            ProcessorState.opVal, hrax₁, encode, num_shift, Nat.shiftLeft_eq]
          omega
        · simp [processDirective, ProcessorState.setReg, hstack₁]
      case h_2 => contradiction

  | Expr.Add1 e, v, st, h =>
    by
      simp only [interpret_expr] at h
      split at h
      case h_1 i he =>
        simp only [Option.some.injEq] at h
        subst h
        obtain ⟨st₁, hrun₁, hrax₁, hstack₁⟩ := compile_expr_spec e (Integer i) st he
        refine ⟨processDirective st₁ (Directive.Add (Reg Rax, Imm (1 <<< num_shift))), ?_, ?_, ?_⟩
        · intro rest
          simp [compile_expr, hrun₁, ProcessorState.skip]
        · simp [processDirective, ProcessorState.setReg, ProcessorState.regVal,
            ProcessorState.opVal, hrax₁, encode, num_shift, Nat.shiftLeft_eq]
          omega
        · simp [processDirective, ProcessorState.setReg, hstack₁]
      case h_2 => contradiction

  | Expr.Add e₁ e₂, v, st, h =>
    by
      simp only [interpret_expr] at h
      split at h
      case h_1 i₁ i₂ he₁ he₂ =>
        simp only [Option.some.injEq] at h
        subst h
        -- run e₁, push its value, run e₂, pop e₁'s value into rcx, add
        obtain ⟨st₁, hrun₁, hrax₁, hstack₁⟩ := compile_expr_spec e₁ (Integer i₁) st he₁
        obtain ⟨st₂, hrun₂, hrax₂, hstack₂⟩ :=
          compile_expr_spec e₂ (Integer i₂) (processDirective st₁ (Push (Reg Rax))) he₂
        refine ⟨processDirective (processDirective st₂ (Pop Rcx))
                  (Directive.Add (Reg Rax, Reg Rcx)), ?_, ?_, ?_⟩
        · intro rest
          simp [compile_expr, hrun₁, hrun₂, ProcessorState.skip]
        · simp [processDirective, ProcessorState.stackPush, ProcessorState.stackPop,
            ProcessorState.setReg, ProcessorState.regVal, ProcessorState.opVal, hstack₂,
            hrax₁, hrax₂, encode, num_shift, Nat.shiftLeft_eq]
          omega
        · simp [processDirective, ProcessorState.stackPush, ProcessorState.stackPop,
            ProcessorState.setReg, ProcessorState.regVal, ProcessorState.opVal, hstack₂,
            hstack₁]
      case h_2 => contradiction

  | Expr.Sub e₁ e₂, v, st, h =>
    by
      simp only [interpret_expr] at h
      split at h
      case h_1 i₁ i₂ he₁ he₂ =>
        simp only [Option.some.injEq] at h
        subst h
        -- run e₁, push its value, run e₂, pop e₁'s value into rcx, subtract, move to rax
        obtain ⟨st₁, hrun₁, hrax₁, hstack₁⟩ := compile_expr_spec e₁ (Integer i₁) st he₁
        obtain ⟨st₂, hrun₂, hrax₂, hstack₂⟩ :=
          compile_expr_spec e₂ (Integer i₂) (processDirective st₁ (Push (Reg Rax))) he₂
        refine ⟨processDirective
                  (processDirective (processDirective st₂ (Pop Rcx))
                    (Directive.Sub (Reg Rcx, Reg Rax)))
                  (Mov (Reg Rax, Reg Rcx)), ?_, ?_, ?_⟩
        · intro rest
          simp [compile_expr, hrun₁, hrun₂, ProcessorState.skip]
        · simp [processDirective, ProcessorState.stackPush, ProcessorState.stackPop,
            ProcessorState.setReg, ProcessorState.regVal, ProcessorState.opVal, hstack₂,
            hrax₁, hrax₂, encode, num_shift, Nat.shiftLeft_eq]
          omega
        · simp [processDirective, ProcessorState.stackPush, ProcessorState.stackPop,
            ProcessorState.setReg, ProcessorState.regVal, ProcessorState.opVal, hstack₂,
            hstack₁]
      case h_2 => contradiction

  | IsZero e, v, st, h =>
    by
      simp only [interpret_expr] at h
      split at h
      case h_1 i he =>
        simp only [Option.some.injEq] at h
        subst h
        obtain ⟨st₁, hrun₁, hrax₁, hstack₁⟩ := compile_expr_spec e (Integer i) st he
        -- compare against 0, then set rax to true and skip over setting it to false if equal
        let st₂ := processDirective st₁ (Cmp (Reg Rax, Imm 0))
        let st₃ := processDirective st₂ (Mov (Reg Rax, Imm true_val))
        have hzf : st₂.zf = decide (i = 0) :=
          by
            simp [st₂, processDirective, ProcessorState.opVal, ProcessorState.regVal, hrax₁,
              encode, num_shift, Nat.shiftLeft_eq]
            by_cases hi : i = 0 <;> simp [hi] <;> omega
        by_cases hi : i = 0
        · refine ⟨st₃, ?_, ?_, ?_⟩
          · intro rest
            simp [compile_expr, hrun₁, ProcessorState.skip, st₃, st₂, hzf, hi]
          · simp [st₃, processDirective, ProcessorState.setReg, ProcessorState.opVal, encode, hi]
          · simp [st₃, st₂, processDirective, ProcessorState.setReg, hstack₁]
        · refine ⟨processDirective st₃ (Mov (Reg Rax, Imm false_val)), ?_, ?_, ?_⟩
          · intro rest
            simp [compile_expr, hrun₁, ProcessorState.skip, st₃, st₂, hzf, hi]
          · simp [st₃, processDirective, ProcessorState.setReg, ProcessorState.opVal, encode, hi]
          · simp [st₃, st₂, processDirective, ProcessorState.setReg, hstack₁]
      case h_2 => contradiction

  | Lt e₁ e₂, v, st, h =>
    by
      simp only [interpret_expr] at h
      split at h
      case h_1 i₁ i₂ he₁ he₂ =>
        simp only [Option.some.injEq] at h
        subst h
        obtain ⟨st₁, hrun₁, hrax₁, hstack₁⟩ := compile_expr_spec e₁ (Integer i₁) st he₁
        obtain ⟨st₂, hrun₂, hrax₂, hstack₂⟩ :=
          compile_expr_spec e₂ (Integer i₂) (processDirective st₁ (Push (Reg Rax))) he₂
        -- pop e₁'s value into rcx, compare it with e₂'s value, then set rax to true and skip
        -- over setting it to false if it was below
        let st₃ := processDirective (processDirective st₂ (Pop Rcx)) (Cmp (Reg Rcx, Reg Rax))
        let st₄ := processDirective st₃ (Mov (Reg Rax, Imm true_val))
        have hcf : st₃.cf = decide (i₁ < i₂) :=
          by
            simp [st₃, processDirective, ProcessorState.stackPush, ProcessorState.stackPop,
              ProcessorState.setReg, ProcessorState.regVal, ProcessorState.opVal, hstack₂,
              hrax₁, hrax₂, encode, num_shift, Nat.shiftLeft_eq]
        have hstack₃ : st₃.stack = st.stack :=
          by
            simp [st₃, processDirective, ProcessorState.stackPush, ProcessorState.stackPop,
              ProcessorState.setReg, hstack₂, hstack₁]
        by_cases hlt : i₁ < i₂
        · refine ⟨st₄, ?_, ?_, ?_⟩
          · intro rest
            simp [compile_expr, hrun₁, hrun₂, ProcessorState.skip, st₄, st₃, hcf, hlt]
          · simp [st₄, processDirective, ProcessorState.setReg, ProcessorState.opVal, encode, hlt]
          · simp [st₄, processDirective, ProcessorState.setReg, hstack₃]
        · refine ⟨processDirective st₄ (Mov (Reg Rax, Imm false_val)), ?_, ?_, ?_⟩
          · intro rest
            simp [compile_expr, hrun₁, hrun₂, ProcessorState.skip, st₄, st₃, hcf, hlt]
          · simp [st₄, processDirective, ProcessorState.setReg, ProcessorState.opVal, encode, hlt]
          · simp [st₄, processDirective, ProcessorState.setReg, hstack₃]
      case h_2 => contradiction

  | If c t f, v, st, h =>
    by
      simp only [interpret_expr] at h
      split at h
      case h_1 hc =>
        -- c is true: the `Je` falls through into t, then the `Jmp` skips over f
        obtain ⟨st₁, hrun₁, hrax₁, hstack₁⟩ := compile_expr_spec c (Boolean true) st hc
        let st₂ := processDirective st₁ (Cmp (Reg Rax, Imm false_val))
        have hzf : st₂.zf = false :=
          by
            simp [st₂, processDirective, ProcessorState.opVal, ProcessorState.regVal, hrax₁,
              encode, true_val, false_val, bool_shift, bool_tag]
        obtain ⟨st₃, hrun₃, hrax₃, hstack₃⟩ := compile_expr_spec t v st₂ h
        refine ⟨st₃, ?_, hrax₃, ?_⟩
        · intro rest
          simp [compile_expr, hrun₁, ProcessorState.skip, st₂, hzf, hrun₃]
        · simp [hstack₃, st₂, processDirective, hstack₁]
      case h_2 hc =>
        -- c is false: the `Je` skips over t (and the `Jmp`) straight to f
        obtain ⟨st₁, hrun₁, hrax₁, hstack₁⟩ := compile_expr_spec c (Boolean false) st hc
        let st₂ := processDirective st₁ (Cmp (Reg Rax, Imm false_val))
        have hzf : st₂.zf = true :=
          by
            simp [st₂, processDirective, ProcessorState.opVal, ProcessorState.regVal, hrax₁,
              encode]
        obtain ⟨st₃, hrun₃, hrax₃, hstack₃⟩ := compile_expr_spec f v st₂ h
        refine ⟨st₃, ?_, hrax₃, ?_⟩
        · intro rest
          simp [compile_expr, hrun₁, ProcessorState.skip, st₂, hzf, List.drop_length_add_append,
            hrun₃]
        · simp [hstack₃, st₂, processDirective, hstack₁]
      case h_3 => contradiction


-- the compiler will produce the same value when the interpreter produces a some
theorem correctness : ∀ prog : Expr,
  (interpret_expr prog).isSome →
  Processor.evalToValue (compile_expr prog) = interpret_expr prog :=
  by
    intro prog hsome
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hsome
    obtain ⟨st', hrun, hrax, _⟩ :=
      compile_expr_spec prog v { rax := 0, rcx := 0, stack := [], zf := false, cf := false } hv
    have hstate : Processor.evalToState (compile_expr prog) = st' :=
      by
        simpa [Processor.evalToState] using hrun []
    rw [hv, evalToValue_encode _ v (by rw [hstate, hrax])]
