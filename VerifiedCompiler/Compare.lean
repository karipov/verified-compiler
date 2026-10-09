import VerifiedCompiler.Process
import VerifiedCompiler.Compile
import VerifiedCompiler.Interpret

open Value Expr Directive Operand Register

def Processor.evalToValue (ds : List Directive) : Option Value :=
  match Processor.eval ds with
  | some (Sum.inl n) => some (Integer n)
  | some (Sum.inr b) => some (Boolean b)
  | none => none


/- ## Running code -/

@[simp] theorem Processor.run_nil (st : ProcessorState) : Processor.run st [] = some st :=
  by
    rw [Processor.run]

@[simp] theorem Processor.run_error (st : ProcessorState) (rest : List Directive) :
  Processor.run st (Error :: rest) = none :=
  by
    rw [Processor.run]

@[simp] theorem Processor.run_cons (st : ProcessorState) (d : Directive) (rest : List Directive)
  (h : d ≠ Error) :
  Processor.run st (d :: rest) = Processor.run (processDirective st d) (rest.drop (st.skip d)) :=
  by
    rw [Processor.run]
    cases d <;> simp_all

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

theorem push_stack (st : ProcessorState) :
  (processDirective st (Push (Reg Rax))).stack = st.rax :: st.stack := rfl


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

-- the tag checks work: masking off the tag bits of a value and comparing them against
-- `num_tag` accepts every number and rejects every boolean...
theorem num_tag_check (v : Value) : (encode v &&& num_mask == num_tag) = v.isNum :=
  by
    cases v with
    | Integer n =>
      have hmod := Nat.and_two_pow_sub_one_eq_mod (n <<< num_shift) 2
      simp [encode, num_shift, num_mask, num_tag, Value.isNum, Nat.shiftLeft_eq] at hmod ⊢
      omega
    | Boolean b =>
      cases b <;> simp [encode, num_mask, num_tag, Value.isNum, true_val, false_val, bool_shift,
        bool_tag]

-- ...and comparing them against `bool_tag` accepts every boolean and rejects every number.
-- (a number's encoding ends in 0b00 and `bool_tag` ends in 0b11, so they can't match)
theorem bool_tag_check (v : Value) : (encode v &&& bool_mask == bool_tag) = v.isBool :=
  by
    cases v with
    | Integer n =>
      have hmod := Nat.and_two_pow_sub_one_eq_mod (n <<< num_shift) 7
      simp [encode, bool_mask, bool_tag, Value.isBool, num_shift, Nat.shiftLeft_eq] at hmod ⊢
      omega
    | Boolean b =>
      cases b <;> simp [encode, bool_mask, bool_tag, Value.isBool, true_val, false_val, bool_shift]

-- different values have different encodings, so `Eq` can just compare encodings
theorem encode_eq (v₁ v₂ : Value) : (encode v₁ == encode v₂) = decide (v₁ = v₂) :=
  by
    cases v₁ with
    | Integer n₁ =>
      cases v₂ with
      | Integer n₂ =>
        by_cases h : n₁ = n₂
        · simp [h]
        · simp [encode, num_shift, Nat.shiftLeft_eq, h]
          omega
      | Boolean b₂ =>
        cases b₂ <;> simp [encode, num_shift, Nat.shiftLeft_eq, true_val, false_val, bool_shift,
          bool_tag] <;> omega
    | Boolean b₁ =>
      cases v₂ with
      | Integer n₂ =>
        cases b₁ <;> simp [encode, num_shift, Nat.shiftLeft_eq, true_val, false_val, bool_shift,
          bool_tag] <;> omega
      | Boolean b₂ =>
        cases b₁ <;> cases b₂ <;> simp [encode, true_val, false_val, bool_shift, bool_tag]

-- untagging an encoded value gives back the value
theorem evalToValue_encode (ds : List Directive) (st : ProcessorState) (v : Value)
  (h : Processor.evalToState ds = some st) (hrax : st.rax = encode v) :
  Processor.evalToValue ds = some v :=
  by
    cases v with
    | Integer n =>
      simp only [Processor.evalToValue, Processor.eval, h, Processor.decode, hrax, encode,
        num_shift, num_mask, num_tag]
      rw [Nat.shiftLeft_eq, land_helper, smth]
      rfl
    | Boolean b =>
      cases b <;> simp [Processor.evalToValue, Processor.eval, h, Processor.decode, hrax, encode,
        num_mask, num_tag, bool_shift, bool_mask, bool_tag, true_val, false_val]


/- ## Type checks -/

theorem tag_test_spec (st : ProcessorState) (mask tag : Nat) :
  ∃ st', (∀ rest, Processor.run st (tag_test mask tag ++ rest) = Processor.run st' rest) ∧
    st'.zf = (st.rax &&& mask == tag) ∧ st'.rax = st.rax ∧ st'.stack = st.stack :=
  by
    refine ⟨processDirective
              (processDirective (processDirective st (Mov (Reg R8, Reg Rax)))
                (Directive.And (Reg R8, Imm mask)))
              (Cmp (Reg R8, Imm tag)), ?_, ?_, ?_, ?_⟩
    · intro rest
      simp [tag_test, ProcessorState.skip]
    all_goals simp [processDirective, ProcessorState.setReg, ProcessorState.regVal,
      ProcessorState.opVal]

-- if the tag matches, `ensure` falls through and leaves rax and the stack alone
theorem ensure_ok (st : ProcessorState) (mask tag : Nat) (h : (st.rax &&& mask == tag) = true) :
  ∃ st', (∀ rest, Processor.run st (ensure mask tag ++ rest) = Processor.run st' rest) ∧
    st'.rax = st.rax ∧ st'.stack = st.stack :=
  by
    obtain ⟨st₁, hrun, hzf, hrax, hstack⟩ := tag_test_spec st mask tag
    refine ⟨st₁, ?_, hrax, hstack⟩
    intro rest
    simp [ensure, hrun, ProcessorState.skip, hzf, h]

-- if it doesn't, the program ends in an error
theorem ensure_err (st : ProcessorState) (mask tag : Nat) (h : (st.rax &&& mask == tag) = false) :
  ∀ rest, Processor.run st (ensure mask tag ++ rest) = none :=
  by
    obtain ⟨st₁, hrun, hzf, hrax, hstack⟩ := tag_test_spec st mask tag
    intro rest
    simp [ensure, hrun, ProcessorState.skip, hzf, h]

theorem ensure_num_ok (st : ProcessorState) (n : Nat) (h : st.rax = encode (Integer n)) :
  ∃ st', (∀ rest, Processor.run st (ensure_num ++ rest) = Processor.run st' rest) ∧
    st'.rax = st.rax ∧ st'.stack = st.stack :=
  ensure_ok st _ _ (by rw [h, num_tag_check]; rfl)

theorem ensure_num_err (st : ProcessorState) (b : Bool) (h : st.rax = encode (Boolean b)) :
  ∀ rest, Processor.run st (ensure_num ++ rest) = none :=
  ensure_err st _ _ (by rw [h, num_tag_check]; rfl)

theorem ensure_bool_ok (st : ProcessorState) (b : Bool) (h : st.rax = encode (Boolean b)) :
  ∃ st', (∀ rest, Processor.run st (ensure_bool ++ rest) = Processor.run st' rest) ∧
    st'.rax = st.rax ∧ st'.stack = st.stack :=
  ensure_ok st _ _ (by rw [h, bool_tag_check]; rfl)

theorem ensure_bool_err (st : ProcessorState) (n : Nat) (h : st.rax = encode (Integer n)) :
  ∀ rest, Processor.run st (ensure_bool ++ rest) = none :=
  ensure_err st _ _ (by rw [h, bool_tag_check]; rfl)

theorem zf_to_bool_spec (st : ProcessorState) :
  ∃ st', (∀ rest, Processor.run st (zf_to_bool ++ rest) = Processor.run st' rest) ∧
    st'.rax = encode (Boolean st.zf) ∧ st'.stack = st.stack :=
  by
    let st₁ := processDirective st (Mov (Reg Rax, Imm true_val))
    cases hzf : st.zf
    · refine ⟨processDirective st₁ (Mov (Reg Rax, Imm false_val)), ?_, ?_, ?_⟩
      · intro rest
        simp [zf_to_bool, ProcessorState.skip, st₁, hzf]
      all_goals simp [st₁, processDirective, ProcessorState.setReg, ProcessorState.opVal, encode]
    · refine ⟨st₁, ?_, ?_, ?_⟩
      · intro rest
        simp [zf_to_bool, ProcessorState.skip, st₁, hzf]
      all_goals simp [st₁, processDirective, ProcessorState.setReg, ProcessorState.opVal, encode]

theorem cf_to_bool_spec (st : ProcessorState) :
  ∃ st', (∀ rest, Processor.run st (cf_to_bool ++ rest) = Processor.run st' rest) ∧
    st'.rax = encode (Boolean st.cf) ∧ st'.stack = st.stack :=
  by
    let st₁ := processDirective st (Mov (Reg Rax, Imm true_val))
    cases hcf : st.cf
    · refine ⟨processDirective st₁ (Mov (Reg Rax, Imm false_val)), ?_, ?_, ?_⟩
      · intro rest
        simp [cf_to_bool, ProcessorState.skip, st₁, hcf]
      all_goals simp [st₁, processDirective, ProcessorState.setReg, ProcessorState.opVal, encode]
    · refine ⟨st₁, ?_, ?_, ?_⟩
      · intro rest
        simp [cf_to_bool, ProcessorState.skip, st₁, hcf]
      all_goals simp [st₁, processDirective, ProcessorState.setReg, ProcessorState.opVal, encode]


/- ## Variables -/

-- the compiler's table agrees with the interpreter's environment: they have the same
-- variables in the same order, and each variable's slot on the stack holds its value
inductive Matches (stack : List Nat) : Env → Symtab → Prop
| nil : Matches stack [] []
| cons {env : Env} {tab : Symtab} {x : String} {v : Value} {i : Nat} :
    stack.reverse[i]? = some (encode v) → Matches stack env tab →
    Matches stack ((x, v) :: env) ((x, i) :: tab)

theorem Matches.lookup_none {s : List Nat} {env : Env} {tab : Symtab} (hm : Matches s env tab)
  (x : String) (h : env.lookup x = none) : tab.lookup x = none :=
  by
    induction hm with
    | nil => rfl
    | @cons env tab y v i hslot hm ih =>
      simp only [List.lookup] at h ⊢
      cases hxy : x == y
      · simp only [hxy] at h ⊢
        exact ih h
      · simp [hxy] at h

theorem Matches.lookup_some {s : List Nat} {env : Env} {tab : Symtab} (hm : Matches s env tab)
  (x : String) (v : Value) (h : env.lookup x = some v) :
  ∃ i, tab.lookup x = some i ∧ s.reverse[i]? = some (encode v) :=
  by
    induction hm with
    | nil => simp [List.lookup] at h
    | @cons env tab y w i hslot hm ih =>
      simp only [List.lookup] at h ⊢
      cases hxy : x == y <;> simp_all

-- slots count up from the bottom of the stack, so pushing doesn't move any of them
theorem Matches.push {s : List Nat} {env : Env} {tab : Symtab} (hm : Matches s env tab) (n : Nat) :
  Matches (n :: s) env tab :=
  by
    induction hm with
    | nil => exact .nil
    | @cons env tab y w i hslot hm ih =>
      refine .cons ?_ ih
      have hi : i < s.reverse.length := by
        obtain ⟨hi, _⟩ := List.getElem?_eq_some_iff.mp hslot
        exact hi
      simp only [List.reverse_cons]
      rw [List.getElem?_append_left hi, hslot]

-- and the value that was just pushed is in the slot right above the old top
theorem slot_push (s : List Nat) (n : Nat) : (n :: s).reverse[s.length]? = some n :=
  by
    simp


/- ## Correctness -/

-- what it means for `code` to do what the interpreter does when it answers `r`. on an error,
-- the code ends in an error no matter what comes after it. on a value `v`, the code falls
-- through to whatever comes after it, with `v`'s encoding in rax and the stack it started with
def Runs (st : ProcessorState) (code : List Directive) : Option Value → Prop
| none => ∀ rest, Processor.run st (code ++ rest) = none
| some v => ∃ st', (∀ rest, Processor.run st (code ++ rest) = Processor.run st' rest) ∧
    st'.rax = encode v ∧ st'.stack = st.stack

-- the compiled code for a subexpression is always followed by more code, and with jumps
-- around we need to know that control actually makes it to that code (or that the program
-- stops with an error). so the induction is done on `Runs`, starting from any state whose
-- stack has the variables of `env` in the slots `tab` gives them
theorem compile_expr_spec :
  ∀ (prog : Expr) (env : Env) (tab : Symtab) (depth : Nat) (st : ProcessorState),
    Matches st.stack env tab → st.stack.length = depth →
    Runs st (compile_expr tab depth prog) (interpret_expr env prog)
  | Expr.Num n, env, tab, depth, st, hm, hd =>
    by
      simp only [interpret_expr, Runs]
      refine ⟨processDirective st (Mov (Reg Rax, Imm (n <<< num_shift))), ?_, ?_, ?_⟩
      · intro rest
        simp [compile_expr, ProcessorState.skip]
      · simp [processDirective, ProcessorState.setReg, ProcessorState.opVal, encode]
      · simp [processDirective, ProcessorState.setReg]

  | Expr.Bool b, env, tab, depth, st, hm, hd =>
    by
      simp only [interpret_expr, Runs]
      refine ⟨processDirective st (Mov (Reg Rax, Imm (encode (Boolean b)))), ?_, ?_, ?_⟩
      · intro rest
        cases b <;> simp [compile_expr, encode, ProcessorState.skip]
      · simp [processDirective, ProcessorState.setReg, ProcessorState.opVal]
      · simp [processDirective, ProcessorState.setReg]

  | Expr.Sub1 e, env, tab, depth, st, hm, hd =>
    by
      have ih := compile_expr_spec e env tab depth st hm hd
      simp only [interpret_expr]
      cases hv : interpret_expr env e with
      | none =>
        simp only [hv, Runs] at ih ⊢
        intro rest
        simp [compile_expr, ih]
      | some v =>
        simp only [hv, Runs] at ih ⊢
        obtain ⟨st₁, hrun₁, hrax₁, hstack₁⟩ := ih
        cases v with
        | Boolean b =>
          intro rest
          simp [compile_expr, hrun₁, ensure_num_err st₁ b hrax₁]
        | Integer i =>
          obtain ⟨st₂, hrun₂, hrax₂, hstack₂⟩ := ensure_num_ok st₁ i hrax₁
          refine ⟨processDirective st₂ (Directive.Sub (Reg Rax, Imm (1 <<< num_shift))), ?_, ?_, ?_⟩
          · intro rest
            simp [compile_expr, hrun₁, hrun₂, ProcessorState.skip]
          · simp [processDirective, ProcessorState.setReg, ProcessorState.regVal,
              ProcessorState.opVal, hrax₂, hrax₁, encode, num_shift, Nat.shiftLeft_eq]
            omega
          · simp [processDirective, ProcessorState.setReg, hstack₂, hstack₁]

  | Expr.Add1 e, env, tab, depth, st, hm, hd =>
    by
      have ih := compile_expr_spec e env tab depth st hm hd
      simp only [interpret_expr]
      cases hv : interpret_expr env e with
      | none =>
        simp only [hv, Runs] at ih ⊢
        intro rest
        simp [compile_expr, ih]
      | some v =>
        simp only [hv, Runs] at ih ⊢
        obtain ⟨st₁, hrun₁, hrax₁, hstack₁⟩ := ih
        cases v with
        | Boolean b =>
          intro rest
          simp [compile_expr, hrun₁, ensure_num_err st₁ b hrax₁]
        | Integer i =>
          obtain ⟨st₂, hrun₂, hrax₂, hstack₂⟩ := ensure_num_ok st₁ i hrax₁
          refine ⟨processDirective st₂ (Directive.Add (Reg Rax, Imm (1 <<< num_shift))), ?_, ?_, ?_⟩
          · intro rest
            simp [compile_expr, hrun₁, hrun₂, ProcessorState.skip]
          · simp [processDirective, ProcessorState.setReg, ProcessorState.regVal,
              ProcessorState.opVal, hrax₂, hrax₁, encode, num_shift, Nat.shiftLeft_eq]
            omega
          · simp [processDirective, ProcessorState.setReg, hstack₂, hstack₁]

  | Expr.Add e₁ e₂, env, tab, depth, st, hm, hd =>
    by
      have ih₁ := compile_expr_spec e₁ env tab depth st hm hd
      simp only [interpret_expr]
      cases hv₁ : interpret_expr env e₁ with
      | none =>
        simp only [hv₁, Runs] at ih₁ ⊢
        intro rest
        simp [compile_expr, ih₁]
      | some v₁ =>
        simp only [hv₁, Runs] at ih₁
        obtain ⟨st₁, hrun₁, hrax₁, hstack₁⟩ := ih₁
        cases v₁ with
        | Boolean b =>
          simp only [Runs]
          intro rest
          simp [compile_expr, hrun₁, ensure_num_err st₁ b hrax₁]
        | Integer i₁ =>
          obtain ⟨st₂, hrun₂, hrax₂, hstack₂⟩ := ensure_num_ok st₁ i₁ hrax₁
          -- push e₁'s value, then e₂ runs with one more slot on the stack
          have ih₂ := compile_expr_spec e₂ env tab (depth + 1)
            (processDirective st₂ (Push (Reg Rax)))
            (by rw [push_stack, hstack₂, hstack₁]; exact hm.push _)
            (by rw [push_stack, hstack₂, hstack₁, List.length_cons, hd])
          cases hv₂ : interpret_expr env e₂ with
          | none =>
            simp only [hv₂, Runs] at ih₂ ⊢
            intro rest
            simp [compile_expr, hrun₁, hrun₂, ProcessorState.skip, ih₂]
          | some v₂ =>
            simp only [hv₂, Runs] at ih₂ ⊢
            obtain ⟨st₃, hrun₃, hrax₃, hstack₃⟩ := ih₂
            cases v₂ with
            | Boolean b =>
              intro rest
              simp [compile_expr, hrun₁, hrun₂, ProcessorState.skip, hrun₃,
                ensure_num_err st₃ b hrax₃]
            | Integer i₂ =>
              obtain ⟨st₄, hrun₄, hrax₄, hstack₄⟩ := ensure_num_ok st₃ i₂ hrax₃
              -- pop e₁'s value into rcx and add
              refine ⟨processDirective (processDirective st₄ (Pop Rcx))
                        (Directive.Add (Reg Rax, Reg Rcx)), ?_, ?_, ?_⟩
              · intro rest
                simp [compile_expr, hrun₁, hrun₂, hrun₃, hrun₄, ProcessorState.skip]
              · simp [processDirective, ProcessorState.stackPush, ProcessorState.stackPop,
                  ProcessorState.setReg, ProcessorState.regVal, ProcessorState.opVal, hstack₄,
                  hstack₃, hrax₄, hrax₃, hrax₂, hrax₁, encode, num_shift, Nat.shiftLeft_eq]
                omega
              · simp [processDirective, ProcessorState.stackPush, ProcessorState.stackPop,
                  ProcessorState.setReg, ProcessorState.regVal, ProcessorState.opVal, hstack₄,
                  hstack₃, hstack₂, hstack₁]


  | Expr.Sub e₁ e₂, env, tab, depth, st, hm, hd =>
    by
      have ih₁ := compile_expr_spec e₁ env tab depth st hm hd
      simp only [interpret_expr]
      cases hv₁ : interpret_expr env e₁ with
      | none =>
        simp only [hv₁, Runs] at ih₁ ⊢
        intro rest
        simp [compile_expr, ih₁]
      | some v₁ =>
        simp only [hv₁, Runs] at ih₁
        obtain ⟨st₁, hrun₁, hrax₁, hstack₁⟩ := ih₁
        cases v₁ with
        | Boolean b =>
          simp only [Runs]
          intro rest
          simp [compile_expr, hrun₁, ensure_num_err st₁ b hrax₁]
        | Integer i₁ =>
          obtain ⟨st₂, hrun₂, hrax₂, hstack₂⟩ := ensure_num_ok st₁ i₁ hrax₁
          have ih₂ := compile_expr_spec e₂ env tab (depth + 1)
            (processDirective st₂ (Push (Reg Rax)))
            (by rw [push_stack, hstack₂, hstack₁]; exact hm.push _)
            (by rw [push_stack, hstack₂, hstack₁, List.length_cons, hd])
          cases hv₂ : interpret_expr env e₂ with
          | none =>
            simp only [hv₂, Runs] at ih₂ ⊢
            intro rest
            simp [compile_expr, hrun₁, hrun₂, ProcessorState.skip, ih₂]
          | some v₂ =>
            simp only [hv₂, Runs] at ih₂ ⊢
            obtain ⟨st₃, hrun₃, hrax₃, hstack₃⟩ := ih₂
            cases v₂ with
            | Boolean b =>
              intro rest
              simp [compile_expr, hrun₁, hrun₂, ProcessorState.skip, hrun₃,
                ensure_num_err st₃ b hrax₃]
            | Integer i₂ =>
              obtain ⟨st₄, hrun₄, hrax₄, hstack₄⟩ := ensure_num_ok st₃ i₂ hrax₃
              -- pop e₁'s value into rcx, subtract, move to rax
              refine ⟨processDirective
                        (processDirective (processDirective st₄ (Pop Rcx))
                          (Directive.Sub (Reg Rcx, Reg Rax)))
                        (Mov (Reg Rax, Reg Rcx)), ?_, ?_, ?_⟩
              · intro rest
                simp [compile_expr, hrun₁, hrun₂, hrun₃, hrun₄, ProcessorState.skip]
              · simp [processDirective, ProcessorState.stackPush, ProcessorState.stackPop,
                  ProcessorState.setReg, ProcessorState.regVal, ProcessorState.opVal, hstack₄,
                  hstack₃, hrax₄, hrax₃, hrax₂, hrax₁, encode, num_shift, Nat.shiftLeft_eq]
                omega
              · simp [processDirective, ProcessorState.stackPush, ProcessorState.stackPop,
                  ProcessorState.setReg, ProcessorState.regVal, ProcessorState.opVal, hstack₄,
                  hstack₃, hstack₂, hstack₁]

  | IsZero e, env, tab, depth, st, hm, hd =>
    by
      have ih := compile_expr_spec e env tab depth st hm hd
      simp only [interpret_expr]
      cases hv : interpret_expr env e with
      | none =>
        simp only [hv, Runs] at ih ⊢
        intro rest
        simp [compile_expr, ih]
      | some v =>
        simp only [hv, Runs] at ih ⊢
        obtain ⟨st₁, hrun₁, hrax₁, hstack₁⟩ := ih
        cases v with
        | Boolean b =>
          intro rest
          simp [compile_expr, hrun₁, ensure_num_err st₁ b hrax₁]
        | Integer i =>
          obtain ⟨st₂, hrun₂, hrax₂, hstack₂⟩ := ensure_num_ok st₁ i hrax₁
          -- compare against 0, then turn the zero flag into a boolean
          have hzf : (processDirective st₂ (Cmp (Reg Rax, Imm 0))).zf = decide (i = 0) :=
            by
              simp [processDirective, ProcessorState.opVal, ProcessorState.regVal, hrax₂, hrax₁,
                encode, num_shift, Nat.shiftLeft_eq]
              by_cases hi : i = 0 <;> simp [hi] <;> omega
          obtain ⟨st₃, hrun₃, hrax₃, hstack₃⟩ :=
            zf_to_bool_spec (processDirective st₂ (Cmp (Reg Rax, Imm 0)))
          refine ⟨st₃, ?_, ?_, ?_⟩
          · intro rest
            simp [compile_expr, hrun₁, hrun₂, ProcessorState.skip, hrun₃]
          · rw [hrax₃, hzf]
          · simp [hstack₃, processDirective, hstack₂, hstack₁]

  | Lt e₁ e₂, env, tab, depth, st, hm, hd =>
    by
      have ih₁ := compile_expr_spec e₁ env tab depth st hm hd
      simp only [interpret_expr]
      cases hv₁ : interpret_expr env e₁ with
      | none =>
        simp only [hv₁, Runs] at ih₁ ⊢
        intro rest
        simp [compile_expr, ih₁]
      | some v₁ =>
        simp only [hv₁, Runs] at ih₁
        obtain ⟨st₁, hrun₁, hrax₁, hstack₁⟩ := ih₁
        cases v₁ with
        | Boolean b =>
          simp only [Runs]
          intro rest
          simp [compile_expr, hrun₁, ensure_num_err st₁ b hrax₁]
        | Integer i₁ =>
          obtain ⟨st₂, hrun₂, hrax₂, hstack₂⟩ := ensure_num_ok st₁ i₁ hrax₁
          have ih₂ := compile_expr_spec e₂ env tab (depth + 1)
            (processDirective st₂ (Push (Reg Rax)))
            (by rw [push_stack, hstack₂, hstack₁]; exact hm.push _)
            (by rw [push_stack, hstack₂, hstack₁, List.length_cons, hd])
          cases hv₂ : interpret_expr env e₂ with
          | none =>
            simp only [hv₂, Runs] at ih₂ ⊢
            intro rest
            simp [compile_expr, hrun₁, hrun₂, ProcessorState.skip, ih₂]
          | some v₂ =>
            simp only [hv₂, Runs] at ih₂ ⊢
            obtain ⟨st₃, hrun₃, hrax₃, hstack₃⟩ := ih₂
            cases v₂ with
            | Boolean b =>
              intro rest
              simp [compile_expr, hrun₁, hrun₂, ProcessorState.skip, hrun₃,
                ensure_num_err st₃ b hrax₃]
            | Integer i₂ =>
              obtain ⟨st₄, hrun₄, hrax₄, hstack₄⟩ := ensure_num_ok st₃ i₂ hrax₃
              -- pop e₁'s value into rcx, compare it with e₂'s value, then turn the carry flag
              -- into a boolean
              have hcf : (processDirective (processDirective st₄ (Pop Rcx))
                            (Cmp (Reg Rcx, Reg Rax))).cf = decide (i₁ < i₂) :=
                by
                  simp [processDirective, ProcessorState.stackPush, ProcessorState.stackPop,
                    ProcessorState.setReg, ProcessorState.regVal, ProcessorState.opVal, hstack₄,
                    hstack₃, hrax₄, hrax₃, hrax₂, hrax₁, encode, num_shift, Nat.shiftLeft_eq]
              have hstack₅ : (processDirective (processDirective st₄ (Pop Rcx))
                                (Cmp (Reg Rcx, Reg Rax))).stack = st.stack :=
                by
                  simp [processDirective, ProcessorState.stackPush, ProcessorState.stackPop,
                    ProcessorState.setReg, ProcessorState.opVal, hstack₄, hstack₃, hstack₂,
                    hstack₁]
              obtain ⟨st₆, hrun₆, hrax₆, hstack₆⟩ :=
                cf_to_bool_spec (processDirective (processDirective st₄ (Pop Rcx))
                  (Cmp (Reg Rcx, Reg Rax)))
              refine ⟨st₆, ?_, ?_, ?_⟩
              · intro rest
                simp [compile_expr, hrun₁, hrun₂, hrun₃, hrun₄, ProcessorState.skip, hrun₆]
              · rw [hrax₆, hcf]
              · rw [hstack₆, hstack₅]


  | If c t f, env, tab, depth, st, hm, hd =>
    by
      have ihc := compile_expr_spec c env tab depth st hm hd
      simp only [interpret_expr]
      cases hv : interpret_expr env c with
      | none =>
        simp only [hv, Runs] at ihc ⊢
        intro rest
        simp [compile_expr, ihc]
      | some v =>
        simp only [hv, Runs] at ihc
        obtain ⟨st₁, hrun₁, hrax₁, hstack₁⟩ := ihc
        cases v with
        | Integer i =>
          simp only [Runs]
          intro rest
          simp [compile_expr, hrun₁, ensure_bool_err st₁ i hrax₁]
        | Boolean b =>
          obtain ⟨st₂, hrun₂, hrax₂, hstack₂⟩ := ensure_bool_ok st₁ b hrax₁
          -- compare c's value against false
          have hzf : (processDirective st₂ (Cmp (Reg Rax, Imm false_val))).zf = !b :=
            by
              cases b <;> simp [processDirective, ProcessorState.opVal, ProcessorState.regVal,
                hrax₂, hrax₁, encode, true_val, false_val, bool_shift, bool_tag]
          have hstack₃ : (processDirective st₂ (Cmp (Reg Rax, Imm false_val))).stack = st.stack :=
            by
              simp [processDirective, hstack₂, hstack₁]
          cases b with
          | true =>
            -- c is true: the `Je` falls through into t, then the `Jmp` skips over f
            have iht := compile_expr_spec t env tab depth
              (processDirective st₂ (Cmp (Reg Rax, Imm false_val)))
              (by rw [hstack₃]; exact hm) (by rw [hstack₃, hd])
            dsimp only
            cases hvt : interpret_expr env t with
            | none =>
              simp only [hvt, Runs] at iht ⊢
              intro rest
              simp [compile_expr, hrun₁, hrun₂, ProcessorState.skip, hzf, iht]
            | some w =>
              simp only [hvt, Runs] at iht ⊢
              obtain ⟨st₄, hrun₄, hrax₄, hstack₄⟩ := iht
              refine ⟨st₄, ?_, hrax₄, by rw [hstack₄, hstack₃]⟩
              intro rest
              simp [compile_expr, hrun₁, hrun₂, ProcessorState.skip, hzf, hrun₄]
          | false =>
            -- c is false: the `Je` skips over t (and the `Jmp`) straight to f
            have ihf := compile_expr_spec f env tab depth
              (processDirective st₂ (Cmp (Reg Rax, Imm false_val)))
              (by rw [hstack₃]; exact hm) (by rw [hstack₃, hd])
            dsimp only
            cases hvf : interpret_expr env f with
            | none =>
              simp only [hvf, Runs] at ihf ⊢
              intro rest
              simp [compile_expr, hrun₁, hrun₂, ProcessorState.skip, hzf,
                List.drop_length_add_append, ihf]
            | some w =>
              simp only [hvf, Runs] at ihf ⊢
              obtain ⟨st₄, hrun₄, hrax₄, hstack₄⟩ := ihf
              refine ⟨st₄, ?_, hrax₄, by rw [hstack₄, hstack₃]⟩
              intro rest
              simp [compile_expr, hrun₁, hrun₂, ProcessorState.skip, hzf,
                List.drop_length_add_append, hrun₄]

  | Expr.Not e, env, tab, depth, st, hm, hd =>
    by
      have ih := compile_expr_spec e env tab depth st hm hd
      simp only [interpret_expr]
      cases hv : interpret_expr env e with
      | none =>
        simp only [hv, Runs] at ih ⊢
        intro rest
        simp [compile_expr, ih]
      | some v =>
        simp only [hv, Runs] at ih ⊢
        obtain ⟨st₁, hrun₁, hrax₁, hstack₁⟩ := ih
        cases v with
        | Integer i =>
          intro rest
          simp [compile_expr, hrun₁, ensure_bool_err st₁ i hrax₁]
        | Boolean b =>
          obtain ⟨st₂, hrun₂, hrax₂, hstack₂⟩ := ensure_bool_ok st₁ b hrax₁
          -- the value is equal to false exactly when its negation is true
          have hzf : (processDirective st₂ (Cmp (Reg Rax, Imm false_val))).zf = !b :=
            by
              cases b <;> simp [processDirective, ProcessorState.opVal, ProcessorState.regVal,
                hrax₂, hrax₁, encode, true_val, false_val, bool_shift, bool_tag]
          obtain ⟨st₃, hrun₃, hrax₃, hstack₃⟩ :=
            zf_to_bool_spec (processDirective st₂ (Cmp (Reg Rax, Imm false_val)))
          refine ⟨st₃, ?_, ?_, ?_⟩
          · intro rest
            simp [compile_expr, hrun₁, hrun₂, ProcessorState.skip, hrun₃]
          · rw [hrax₃, hzf]
          · simp [hstack₃, processDirective, hstack₂, hstack₁]

  | Expr.Eq e₁ e₂, env, tab, depth, st, hm, hd =>
    by
      have ih₁ := compile_expr_spec e₁ env tab depth st hm hd
      simp only [interpret_expr]
      cases hv₁ : interpret_expr env e₁ with
      | none =>
        simp only [hv₁, Runs] at ih₁ ⊢
        intro rest
        simp [compile_expr, ih₁]
      | some v₁ =>
        simp only [hv₁, Runs] at ih₁
        obtain ⟨st₁, hrun₁, hrax₁, hstack₁⟩ := ih₁
        -- no type checks: push e₁'s value, then e₂ runs with one more slot on the stack
        have ih₂ := compile_expr_spec e₂ env tab (depth + 1)
          (processDirective st₁ (Push (Reg Rax)))
          (by rw [push_stack, hstack₁]; exact hm.push _)
          (by rw [push_stack, hstack₁, List.length_cons, hd])
        cases hv₂ : interpret_expr env e₂ with
        | none =>
          simp only [hv₂, Runs] at ih₂ ⊢
          intro rest
          simp [compile_expr, hrun₁, ProcessorState.skip, ih₂]
        | some v₂ =>
          simp only [hv₂, Runs] at ih₂ ⊢
          obtain ⟨st₂, hrun₂, hrax₂, hstack₂⟩ := ih₂
          -- pop e₁'s value into rcx, then compare the two encodings
          have hzf : (processDirective (processDirective st₂ (Pop Rcx))
                        (Cmp (Reg Rcx, Reg Rax))).zf = decide (v₁ = v₂) :=
            by
              simp only [processDirective, ProcessorState.stackPush, ProcessorState.stackPop,
                hstack₂, ProcessorState.setReg, ProcessorState.opVal, ProcessorState.regVal, hrax₁,
                hrax₂]
              exact encode_eq v₁ v₂
          have hstack₃ : (processDirective (processDirective st₂ (Pop Rcx))
                            (Cmp (Reg Rcx, Reg Rax))).stack = st.stack :=
            by
              simp [processDirective, ProcessorState.stackPush, ProcessorState.stackPop, hstack₂,
                ProcessorState.setReg, hstack₁]
          obtain ⟨st₄, hrun₄, hrax₄, hstack₄⟩ :=
            zf_to_bool_spec (processDirective (processDirective st₂ (Pop Rcx))
              (Cmp (Reg Rcx, Reg Rax)))
          refine ⟨st₄, ?_, ?_, ?_⟩
          · intro rest
            simp [compile_expr, hrun₁, hrun₂, ProcessorState.skip, hrun₄]
          · rw [hrax₄, hzf]
          · rw [hstack₄, hstack₃]


  | Expr.And e₁ e₂, env, tab, depth, st, hm, hd =>
    by
      have ih₁ := compile_expr_spec e₁ env tab depth st hm hd
      simp only [interpret_expr]
      cases hv₁ : interpret_expr env e₁ with
      | none =>
        simp only [hv₁, Runs] at ih₁ ⊢
        intro rest
        simp [compile_expr, ih₁]
      | some v₁ =>
        simp only [hv₁, Runs] at ih₁
        obtain ⟨st₁, hrun₁, hrax₁, hstack₁⟩ := ih₁
        cases v₁ with
        | Integer i =>
          simp only [Runs]
          intro rest
          simp [compile_expr, hrun₁, ensure_bool_err st₁ i hrax₁]
        | Boolean b =>
          obtain ⟨st₂, hrun₂, hrax₂, hstack₂⟩ := ensure_bool_ok st₁ b hrax₁
          have hzf : (processDirective st₂ (Cmp (Reg Rax, Imm false_val))).zf = !b :=
            by
              cases b <;> simp [processDirective, ProcessorState.opVal, ProcessorState.regVal,
                hrax₂, hrax₁, encode, true_val, false_val, bool_shift, bool_tag]
          have hstack₃ : (processDirective st₂ (Cmp (Reg Rax, Imm false_val))).stack = st.stack :=
            by
              simp [processDirective, hstack₂, hstack₁]
          cases b with
          | false =>
            -- e₁ is false, so that's the answer: the `Je` skips over e₂ and rax still holds false
            simp only [Runs]
            refine ⟨processDirective st₂ (Cmp (Reg Rax, Imm false_val)), ?_, ?_, hstack₃⟩
            · intro rest
              simp [compile_expr, hrun₁, hrun₂, ProcessorState.skip, hzf]
            · simp [processDirective, hrax₂, hrax₁]
          | true =>
            -- e₁ is true, so the answer is whatever e₂ is
            have ih₂ := compile_expr_spec e₂ env tab depth
              (processDirective st₂ (Cmp (Reg Rax, Imm false_val)))
              (by rw [hstack₃]; exact hm) (by rw [hstack₃, hd])
            dsimp only
            cases hv₂ : interpret_expr env e₂ with
            | none =>
              simp only [hv₂, Runs] at ih₂ ⊢
              intro rest
              simp [compile_expr, hrun₁, hrun₂, ProcessorState.skip, hzf, ih₂]
            | some v₂ =>
              simp only [hv₂, Runs] at ih₂ ⊢
              obtain ⟨st₄, hrun₄, hrax₄, hstack₄⟩ := ih₂
              cases v₂ with
              | Integer i =>
                intro rest
                simp [compile_expr, hrun₁, hrun₂, ProcessorState.skip, hzf, hrun₄,
                  ensure_bool_err st₄ i hrax₄]
              | Boolean b₂ =>
                obtain ⟨st₅, hrun₅, hrax₅, hstack₅⟩ := ensure_bool_ok st₄ b₂ hrax₄
                refine ⟨st₅, ?_, by rw [hrax₅, hrax₄], by rw [hstack₅, hstack₄, hstack₃]⟩
                intro rest
                simp [compile_expr, hrun₁, hrun₂, ProcessorState.skip, hzf, hrun₄, hrun₅]

  | Expr.Or e₁ e₂, env, tab, depth, st, hm, hd =>
    by
      have ih₁ := compile_expr_spec e₁ env tab depth st hm hd
      simp only [interpret_expr]
      cases hv₁ : interpret_expr env e₁ with
      | none =>
        simp only [hv₁, Runs] at ih₁ ⊢
        intro rest
        simp [compile_expr, ih₁]
      | some v₁ =>
        simp only [hv₁, Runs] at ih₁
        obtain ⟨st₁, hrun₁, hrax₁, hstack₁⟩ := ih₁
        cases v₁ with
        | Integer i =>
          simp only [Runs]
          intro rest
          simp [compile_expr, hrun₁, ensure_bool_err st₁ i hrax₁]
        | Boolean b =>
          obtain ⟨st₂, hrun₂, hrax₂, hstack₂⟩ := ensure_bool_ok st₁ b hrax₁
          have hzf : (processDirective st₂ (Cmp (Reg Rax, Imm true_val))).zf = b :=
            by
              cases b <;> simp [processDirective, ProcessorState.opVal, ProcessorState.regVal,
                hrax₂, hrax₁, encode, true_val, false_val, bool_shift, bool_tag]
          have hstack₃ : (processDirective st₂ (Cmp (Reg Rax, Imm true_val))).stack = st.stack :=
            by
              simp [processDirective, hstack₂, hstack₁]
          cases b with
          | true =>
            -- e₁ is true, so that's the answer: the `Je` skips over e₂ and rax still holds true
            simp only [Runs]
            refine ⟨processDirective st₂ (Cmp (Reg Rax, Imm true_val)), ?_, ?_, hstack₃⟩
            · intro rest
              simp [compile_expr, hrun₁, hrun₂, ProcessorState.skip, hzf]
            · simp [processDirective, hrax₂, hrax₁]
          | false =>
            -- e₁ is false, so the answer is whatever e₂ is
            have ih₂ := compile_expr_spec e₂ env tab depth
              (processDirective st₂ (Cmp (Reg Rax, Imm true_val)))
              (by rw [hstack₃]; exact hm) (by rw [hstack₃, hd])
            dsimp only
            cases hv₂ : interpret_expr env e₂ with
            | none =>
              simp only [hv₂, Runs] at ih₂ ⊢
              intro rest
              simp [compile_expr, hrun₁, hrun₂, ProcessorState.skip, hzf, ih₂]
            | some v₂ =>
              simp only [hv₂, Runs] at ih₂ ⊢
              obtain ⟨st₄, hrun₄, hrax₄, hstack₄⟩ := ih₂
              cases v₂ with
              | Integer i =>
                intro rest
                simp [compile_expr, hrun₁, hrun₂, ProcessorState.skip, hzf, hrun₄,
                  ensure_bool_err st₄ i hrax₄]
              | Boolean b₂ =>
                obtain ⟨st₅, hrun₅, hrax₅, hstack₅⟩ := ensure_bool_ok st₄ b₂ hrax₄
                refine ⟨st₅, ?_, by rw [hrax₅, hrax₄], by rw [hstack₅, hstack₄, hstack₃]⟩
                intro rest
                simp [compile_expr, hrun₁, hrun₂, ProcessorState.skip, hzf, hrun₄, hrun₅]

  | IsNum e, env, tab, depth, st, hm, hd =>
    by
      have ih := compile_expr_spec e env tab depth st hm hd
      simp only [interpret_expr]
      cases hv : interpret_expr env e with
      | none =>
        simp only [hv, Runs] at ih ⊢
        intro rest
        simp [compile_expr, ih]
      | some v =>
        simp only [hv, Runs] at ih ⊢
        obtain ⟨st₁, hrun₁, hrax₁, hstack₁⟩ := ih
        -- the same test that `ensure` does, but its answer goes in rax instead of deciding
        -- whether to call the error handler
        obtain ⟨st₂, hrun₂, hzf₂, hrax₂, hstack₂⟩ := tag_test_spec st₁ num_mask num_tag
        obtain ⟨st₃, hrun₃, hrax₃, hstack₃⟩ := zf_to_bool_spec st₂
        refine ⟨st₃, ?_, ?_, ?_⟩
        · intro rest
          simp [compile_expr, hrun₁, hrun₂, hrun₃]
        · rw [hrax₃, hzf₂, hrax₁, num_tag_check]
        · rw [hstack₃, hstack₂, hstack₁]

  | IsBool e, env, tab, depth, st, hm, hd =>
    by
      have ih := compile_expr_spec e env tab depth st hm hd
      simp only [interpret_expr]
      cases hv : interpret_expr env e with
      | none =>
        simp only [hv, Runs] at ih ⊢
        intro rest
        simp [compile_expr, ih]
      | some v =>
        simp only [hv, Runs] at ih ⊢
        obtain ⟨st₁, hrun₁, hrax₁, hstack₁⟩ := ih
        -- the same test that `ensure` does, but its answer goes in rax instead of deciding
        -- whether to call the error handler
        obtain ⟨st₂, hrun₂, hzf₂, hrax₂, hstack₂⟩ := tag_test_spec st₁ bool_mask bool_tag
        obtain ⟨st₃, hrun₃, hrax₃, hstack₃⟩ := zf_to_bool_spec st₂
        refine ⟨st₃, ?_, ?_, ?_⟩
        · intro rest
          simp [compile_expr, hrun₁, hrun₂, hrun₃]
        · rw [hrax₃, hzf₂, hrax₁, bool_tag_check]
        · rw [hstack₃, hstack₂, hstack₁]

  | Var x, env, tab, depth, st, hm, hd =>
    by
      simp only [interpret_expr]
      cases hv : env.lookup x with
      | none =>
        -- not in scope for the interpreter, so not in the compiler's table either
        have ht := hm.lookup_none x hv
        simp only [Runs]
        intro rest
        simp [compile_expr, ht]
      | some v =>
        obtain ⟨i, ht, hslot⟩ := hm.lookup_some x v hv
        simp only [Runs]
        refine ⟨processDirective st (Load i), ?_, ?_, ?_⟩
        · intro rest
          simp [compile_expr, ht, ProcessorState.skip]
        · simp [processDirective, ProcessorState.slot, hslot]
        · simp [processDirective]

  | Let x e body, env, tab, depth, st, hm, hd =>
    by
      have ih := compile_expr_spec e env tab depth st hm hd
      simp only [interpret_expr]
      cases hv : interpret_expr env e with
      | none =>
        simp only [hv, Runs] at ih ⊢
        intro rest
        simp [compile_expr, ih]
      | some v =>
        simp only [hv, Runs] at ih
        obtain ⟨st₁, hrun₁, hrax₁, hstack₁⟩ := ih
        -- push e's value, so it's in slot `depth` while the body runs
        have hpush : (processDirective st₁ (Push (Reg Rax))).stack = encode v :: st.stack :=
          by
            rw [push_stack, hrax₁, hstack₁]
        have ihb := compile_expr_spec body ((x, v) :: env) ((x, depth) :: tab) (depth + 1)
          (processDirective st₁ (Push (Reg Rax)))
          (by rw [hpush, ← hd]; exact .cons (slot_push _ _) (hm.push _))
          (by rw [hpush, List.length_cons, hd])
        dsimp only
        cases hvb : interpret_expr ((x, v) :: env) body with
        | none =>
          simp only [hvb, Runs] at ihb ⊢
          intro rest
          simp [compile_expr, hrun₁, ProcessorState.skip, ihb]
        | some w =>
          simp only [hvb, Runs] at ihb ⊢
          obtain ⟨st₂, hrun₂, hrax₂, hstack₂⟩ := ihb
          rw [hpush] at hstack₂
          -- pop the slot back off, which leaves the body's value in rax
          refine ⟨processDirective st₂ (Pop Rcx), ?_, ?_, ?_⟩
          · intro rest
            simp [compile_expr, hrun₁, hrun₂, ProcessorState.skip]
          · simp [processDirective, ProcessorState.stackPop, ProcessorState.setReg, hstack₂, hrax₂]
          · simp [processDirective, ProcessorState.stackPop, ProcessorState.setReg, hstack₂]


-- on every program, the compiled code gives exactly what the interpreter gives: the same
-- value, or an error when the interpreter has one
theorem correctness : ∀ prog : Expr,
  Processor.evalToValue (compile prog) = interpret prog :=
  by
    intro prog
    have h := compile_expr_spec prog [] [] 0
      { rax := 0, rcx := 0, r8 := 0, stack := [], zf := false, cf := false } .nil rfl
    cases hv : interpret prog with
    | none =>
      simp only [interpret] at hv
      simp only [hv, Runs] at h
      have hstate : Processor.evalToState (compile prog) = none :=
        by
          simpa [Processor.evalToState, compile] using h []
      simp [Processor.evalToValue, Processor.eval, hstate]
    | some v =>
      simp only [interpret] at hv
      simp only [hv, Runs] at h
      obtain ⟨st', hrun, hrax, _⟩ := h
      have hstate : Processor.evalToState (compile prog) = some st' :=
        by
          simpa [Processor.evalToState, compile] using hrun []
      exact evalToValue_encode _ st' v hstate hrax
