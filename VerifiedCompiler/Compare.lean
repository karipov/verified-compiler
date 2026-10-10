import VerifiedCompiler.Process

open Value Expr Directive Operand Register


/- ## Running code -/

-- the directives that `Processor.run` handles by `processDirective` and `skip`
def Directive.simple : Directive → Bool
| Error => false
| Ret => false
| Call _ => false
| _ => true

section
variable (funs : List (String × List Directive))

@[simp] theorem Processor.run_nil (fuel : Nat) (st : ProcessorState) :
  Processor.run funs fuel st [] = .done st :=
  by
    rw [Processor.run]

@[simp] theorem Processor.run_error (fuel : Nat) (st : ProcessorState) (rest : List Directive) :
  Processor.run funs fuel st (Error :: rest) = .error :=
  by
    rw [Processor.run]

@[simp] theorem Processor.run_ret (fuel : Nat) (st : ProcessorState) (rest : List Directive) :
  Processor.run funs fuel st (Ret :: rest) = .done { st with stack := st.stack.drop 1 } :=
  by
    rw [Processor.run]

theorem Processor.run_call_zero (st : ProcessorState) (f : String) (rest : List Directive) :
  Processor.run funs 0 st (Call f :: rest) = .timeout :=
  by
    rw [Processor.run]

theorem Processor.run_call (fuel : Nat) (st : ProcessorState) (f : String) (rest : List Directive) :
  Processor.run funs (fuel + 1) st (Call f :: rest) =
    match funs.lookup f with
    | none => .error
    | some body =>
      match Processor.run funs fuel (st.stackPush 0) body with
      | .done st' => Processor.run funs (fuel + 1) st' rest
      | .error => .error
      | .timeout => .timeout :=
  by
    rw [Processor.run]
    rfl

theorem Processor.run_cons (fuel : Nat) (st : ProcessorState) (d : Directive)
  (rest : List Directive) (h : d.simple = true) :
  Processor.run funs fuel st (d :: rest) =
    match st.skip d with
    | none => .error
    | some n => Processor.run funs fuel (processDirective st d) (rest.drop n) :=
  by
    cases d
    all_goals first
      | (simp [Directive.simple] at h; done)
      | (rw [Processor.run] <;> first | rfl | simp)

end


/- ## Specs -/

-- what running `code` from `st` does, when the program should end up with `r`. if `r` is an
-- error or a timeout, that's what happens, whatever comes after the code. if it's `done a`, the
-- code falls through to whatever comes after it, in a state where `P a` holds
def Spec (funs : List (String × List Directive)) (fuel : Nat) {α : Type} (st : ProcessorState)
    (code : List Directive) (P : α → ProcessorState → Prop) : Outcome α → Prop
| .done a => ∃ st', (∀ rest, Processor.run funs fuel st (code ++ rest) =
    Processor.run funs fuel st' rest) ∧ P a st'
| .error => ∀ rest, Processor.run funs fuel st (code ++ rest) = .error
| .timeout => ∀ rest, Processor.run funs fuel st (code ++ rest) = .timeout

section
variable {funs : List (String × List Directive)} {fuel : Nat} {α β : Type}
  {st : ProcessorState} {code c₁ c₂ : List Directive}
  {P : α → ProcessorState → Prop} {Q : β → ProcessorState → Prop} {r : Outcome α}

-- no code: nothing happens
theorem Spec.pure {a : α} (h : P a st) : Spec funs fuel st [] P (.done a) :=
  ⟨st, fun _ => rfl, h⟩

theorem Spec.mono {P' : α → ProcessorState → Prop} (h : Spec funs fuel st code P r)
  (hP : ∀ a s, P a s → P' a s) : Spec funs fuel st code P' r :=
  by
    cases r with
    | done a =>
      obtain ⟨s, hrun, hs⟩ := h
      exact ⟨s, hrun, hP a s hs⟩
    | error => exact h
    | timeout => exact h

-- running one piece of code and then another is the interpreter's `>>=`
theorem Spec.bind {k : α → Outcome β} (h₁ : Spec funs fuel st c₁ P r)
  (h₂ : ∀ a s, P a s → Spec funs fuel s c₂ Q (k a)) :
  Spec funs fuel st (c₁ ++ c₂) Q (r >>= k) :=
  by
    cases r with
    | done a =>
      obtain ⟨s, hrun, hs⟩ := h₁
      have h := h₂ a s hs
      simp only [Outcome.done_bind]
      cases hk : k a with
      | done b =>
        rw [hk] at h
        obtain ⟨s', hrun', hs'⟩ := h
        exact ⟨s', fun rest => by rw [List.append_assoc, hrun, hrun'], hs'⟩
      | error =>
        rw [hk] at h
        intro rest
        rw [List.append_assoc, hrun, h]
      | timeout =>
        rw [hk] at h
        intro rest
        rw [List.append_assoc, hrun, h]
    | error =>
      intro rest
      rw [List.append_assoc]
      exact h₁ _
    | timeout =>
      intro rest
      rw [List.append_assoc]
      exact h₁ _

-- the same, when the second piece of code doesn't change the outcome
theorem Spec.then {Q : α → ProcessorState → Prop} (h₁ : Spec funs fuel st c₁ P r)
  (h₂ : ∀ a s, P a s → Spec funs fuel s c₂ Q (.done a)) :
  Spec funs fuel st (c₁ ++ c₂) Q r :=
  by
    have h := Spec.bind (k := Outcome.done) h₁ h₂
    cases r <;> exact h

-- one directive that isn't a call, a return or an error. it skips the next `n` directives
theorem Spec.jump {d : Directive} {n : Nat} (hd : d.simple = true) (hs : st.skip d = some n)
  (hn : n ≤ code.length) (h : Spec funs fuel (processDirective st d) (code.drop n) P r) :
  Spec funs fuel st (d :: code) P r :=
  by
    have key : ∀ rest, Processor.run funs fuel st (d :: code ++ rest) =
        Processor.run funs fuel (processDirective st d) (code.drop n ++ rest) :=
      by
        intro rest
        rw [List.cons_append, Processor.run_cons _ _ _ _ _ hd, hs]
        dsimp only
        rw [List.drop_append_of_le_length hn]
    cases r with
    | done a =>
      obtain ⟨s, hrun, hs⟩ := h
      exact ⟨s, fun rest => by rw [key, hrun], hs⟩
    | error =>
      intro rest
      rw [key]
      exact h rest
    | timeout =>
      intro rest
      rw [key]
      exact h rest

-- the usual case: it doesn't skip anything
theorem Spec.step {d : Directive} (h : Spec funs fuel (processDirective st d) code P r)
  (hd : d.simple = true := by rfl) (hs : st.skip d = some 0 := by rfl) :
  Spec funs fuel st (d :: code) P r :=
  Spec.jump hd hs (Nat.zero_le _) (by simpa using h)

theorem Spec.error_here : Spec funs fuel st (Error :: code) P .error :=
  by
    intro rest
    simp

end


/- ## Values in the heap -/

-- `w` stores the value `v`, in a heap `mem` where everything below `hp` is in use. a pair is a
-- pointer to its two halves, and they were stored before the pair was, so below its address
inductive Encodes (mem : Nat → Nat) : Nat → Value → Nat → Prop
| int (hp n : Nat) : Encodes mem hp (Integer n) (n <<< num_shift)
| bool (hp : Nat) (b : Bool) : Encodes mem hp (Boolean b) (if b then true_val else false_val)
| pair {hp a : Nat} {v₁ v₂ : Value} : a % 8 = 0 → a + 16 ≤ hp →
    Encodes mem a v₁ (mem a) → Encodes mem a v₂ (mem (a + 8)) →
    Encodes mem hp (Pair v₁ v₂) (a + pair_tag)

section
variable {mem : Nat → Nat} {hp : Nat} {v : Value} {w : Nat}

theorem Encodes.int' {n : Nat} (h : w = n <<< num_shift) : Encodes mem hp (Integer n) w :=
  h ▸ .int hp n

theorem Encodes.bool' {b : Bool} (h : w = if b then true_val else false_val) :
  Encodes mem hp (Boolean b) w :=
  h ▸ .bool hp b

theorem Encodes.int_inv {n : Nat} (h : Encodes mem hp (Integer n) w) : w = n <<< num_shift :=
  by
    cases h
    rfl

theorem Encodes.bool_inv {b : Bool} (h : Encodes mem hp (Boolean b) w) :
  w = if b then true_val else false_val :=
  by
    cases h
    rfl

theorem Encodes.pair_inv {v₁ v₂ : Value} (h : Encodes mem hp (Pair v₁ v₂) w) :
  ∃ a, w = a + pair_tag ∧ a % 8 = 0 ∧ a + 16 ≤ hp ∧
    Encodes mem a v₁ (mem a) ∧ Encodes mem a v₂ (mem (a + 8)) :=
  by
    cases h with
    | pair ha hle h₁ h₂ => exact ⟨_, rfl, ha, hle, h₁, h₂⟩

-- storing more things in the heap doesn't change what's already there
theorem Encodes.mono {mem' : Nat → Nat} {hp' : Nat} (h : Encodes mem hp v w) (hhp : hp ≤ hp')
  (hmem : ∀ a, a < hp → mem' a = mem a) : Encodes mem' hp' v w :=
  by
    induction h generalizing hp' with
    | int => exact .int _ _
    | bool => exact .bool _ _
    | @pair hp a v₁ v₂ ha hle h₁ h₂ ih₁ ih₂ =>
      refine .pair ha (by omega) ?_ ?_
      · rw [hmem a (by omega)]
        exact ih₁ (Nat.le_refl _) (fun x hx => hmem x (by omega))
      · rw [hmem (a + 8) (by omega)]
        exact ih₂ (Nat.le_refl _) (fun x hx => hmem x (by omega))

theorem num_mask_eq (w : Nat) : w &&& num_mask = w % 4 := Nat.and_two_pow_sub_one_eq_mod w 2
theorem bool_mask_eq (w : Nat) : w &&& bool_mask = w % 128 := Nat.and_two_pow_sub_one_eq_mod w 7
theorem heap_mask_eq (w : Nat) : w &&& heap_mask = w % 8 := Nat.and_two_pow_sub_one_eq_mod w 3

-- the tag checks work: masking off the tag bits of a value and comparing them against a tag
-- is true exactly for the values with that tag
theorem Encodes.num_check (h : Encodes mem hp v w) : (w &&& num_mask == num_tag) = v.isNum :=
  by
    cases h with
    | int => simp [num_mask_eq, num_tag, Value.isNum, num_shift, Nat.shiftLeft_eq] <;> omega
    | bool _ b => cases b <;> decide
    | pair ha => simp [num_mask_eq, num_tag, Value.isNum, pair_tag] <;> omega

theorem Encodes.bool_check (h : Encodes mem hp v w) : (w &&& bool_mask == bool_tag) = v.isBool :=
  by
    cases h with
    | int => simp [bool_mask_eq, bool_tag, Value.isBool, num_shift, Nat.shiftLeft_eq] <;> omega
    | bool _ b => cases b <;> decide
    | pair ha => simp [bool_mask_eq, bool_tag, Value.isBool, pair_tag] <;> omega

theorem Encodes.pair_check (h : Encodes mem hp v w) : (w &&& heap_mask == pair_tag) = v.isPair :=
  by
    cases h with
    | int => simp [heap_mask_eq, pair_tag, Value.isPair, num_shift, Nat.shiftLeft_eq] <;> omega
    | bool _ b => cases b <;> decide
    | pair ha => simp [heap_mask_eq, pair_tag, Value.isPair] <;> omega

-- numbers and booleans each have one encoding, so `Eq` can compare encodings
theorem Encodes.eq_check {mem' : Nat → Nat} {hp' : Nat} {v' : Value} {w' : Nat}
  (h : Encodes mem hp v w) (h' : Encodes mem' hp' v' w') (hv : v.isPair = false) (hv' : v'.isPair = false) :
  (w == w') = decide (v = v') :=
  by
    cases h <;> cases h' <;> simp_all [Value.isPair]
    case int.int n n' =>
      by_cases hn : n = n'
      · simp [hn]
      · simp [num_shift, Nat.shiftLeft_eq, hn]; omega
    case int.bool n b => cases b <;> simp [num_shift, Nat.shiftLeft_eq, true_val, false_val, bool_shift, bool_tag] <;> omega
    case bool.int b n => cases b <;> simp [num_shift, Nat.shiftLeft_eq, true_val, false_val, bool_shift, bool_tag] <;> omega
    case bool.bool b b' => cases b <;> cases b' <;> decide

-- reading a value back out of the heap gives the value
theorem Encodes.decode (h : Encodes mem hp v w) : ∀ n, hp < n → decode mem n w = v :=
  by
    induction h with
    | int hp k =>
      intro n hn
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      have h4 : k <<< 2 % 4 = 0 := by simp [Nat.shiftLeft_eq] <;> omega
      simp [_root_.decode, num_mask_eq, h4, num_tag, num_shift]
    | bool hp b =>
      intro n hn
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      cases b <;> simp [_root_.decode, true_val, false_val, bool_shift, bool_tag, num_mask, num_tag,
        bool_mask]
    | @pair hp a v₁ v₂ ha hle h₁ h₂ ih₁ ih₂ =>
      intro n hn
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      have hnum : (a + 2) % 4 ≠ 0 := by omega
      have hbool : (a + 2) % 128 ≠ 31 := by omega
      have hpair : (a + 2) % 8 = 2 := by omega
      simp [_root_.decode, num_mask_eq, bool_mask_eq, heap_mask_eq, hnum, hbool, hpair, num_tag,
        bool_tag, pair_tag]
      exact ⟨ih₁ m (by omega), ih₂ m (by omega)⟩

end


/- ## Type checks -/

-- the state after `tag_test`
def checked (s : ProcessorState) (mask tag : Nat) : ProcessorState :=
  { s with r8 := s.rax &&& mask, zf := some (s.rax &&& mask == tag),
           cf := some (decide (s.rax &&& mask < tag)) }

section
variable {funs : List (String × List Directive)} {fuel : Nat} {β : Type} {st : ProcessorState}
  {code : List Directive} {Q : β → ProcessorState → Prop} {r : Outcome β}
  {mem : Nat → Nat} {hp : Nat} {v : Value}

theorem Spec.tag_test {mask tag : Nat} (h : Spec funs fuel (checked st mask tag) code Q r) :
  Spec funs fuel st (tag_test mask tag ++ code) Q r :=
  by
    simp only [_root_.tag_test, List.cons_append, List.nil_append]
    exact Spec.step (Spec.step (Spec.step h))

theorem Spec.ensure {mask tag : Nat}
  (hok : (st.rax &&& mask == tag) = true → Spec funs fuel (checked st mask tag) code Q r)
  (herr : (st.rax &&& mask == tag) = false → r = .error) :
  Spec funs fuel st (ensure mask tag ++ code) Q r :=
  by
    simp only [_root_.ensure, List.append_assoc, List.cons_append, List.nil_append]
    apply Spec.tag_test
    cases hb : (st.rax &&& mask == tag)
    · rw [herr hb]
      exact Spec.step (hs := by simp [ProcessorState.skip, checked, hb]) Spec.error_here
    · exact Spec.jump (n := 1) rfl (by simp [ProcessorState.skip, checked, hb]) (by simp)
        (by simpa [processDirective] using hok hb)

theorem Spec.ensure_not {mask tag : Nat}
  (hok : (st.rax &&& mask == tag) = false → Spec funs fuel (checked st mask tag) code Q r)
  (herr : (st.rax &&& mask == tag) = true → r = .error) :
  Spec funs fuel st (ensure_not mask tag ++ code) Q r :=
  by
    simp only [_root_.ensure_not, List.append_assoc, List.cons_append, List.nil_append]
    apply Spec.tag_test
    cases hb : (st.rax &&& mask == tag)
    · exact Spec.jump (n := 1) rfl (by simp [ProcessorState.skip, checked, hb]) (by simp)
        (by simpa [processDirective] using hok hb)
    · rw [herr hb]
      exact Spec.step (hs := by simp [ProcessorState.skip, checked, hb]) Spec.error_here

theorem Spec.ensure_num {k : Nat → Outcome β} (henc : Encodes mem hp v st.rax)
  (h : ∀ i, v = Integer i → Spec funs fuel (checked st num_mask num_tag) code Q (k i)) :
  Spec funs fuel st (ensure_num ++ code) Q (v.asNum >>= k) :=
  by
    apply Spec.ensure <;> intro hb <;> rw [henc.num_check] at hb <;>
      cases v <;> simp_all [Value.isNum, Value.asNum]

theorem Spec.ensure_bool {k : Bool → Outcome β} (henc : Encodes mem hp v st.rax)
  (h : ∀ b, v = Boolean b → Spec funs fuel (checked st bool_mask bool_tag) code Q (k b)) :
  Spec funs fuel st (ensure_bool ++ code) Q (v.asBool >>= k) :=
  by
    apply Spec.ensure <;> intro hb <;> rw [henc.bool_check] at hb <;>
      cases v <;> simp_all [Value.isBool, Value.asBool]

theorem Spec.ensure_pair {k : Value × Value → Outcome β} (henc : Encodes mem hp v st.rax)
  (h : ∀ v₁ v₂, v = Value.Pair v₁ v₂ → Spec funs fuel (checked st heap_mask pair_tag) code Q (k (v₁, v₂))) :
  Spec funs fuel st (ensure_pair ++ code) Q (v.asPair >>= k) :=
  by
    apply Spec.ensure <;> intro hb <;> rw [henc.pair_check] at hb <;>
      cases v <;> simp_all [Value.isPair, Value.asPair]

theorem Spec.ensure_atom {k : Value → Outcome β} (henc : Encodes mem hp v st.rax)
  (h : v.isPair = false → Spec funs fuel (checked st heap_mask pair_tag) code Q (k v)) :
  Spec funs fuel st (ensure_atom ++ code) Q (v.asAtom >>= k) :=
  by
    apply Spec.ensure_not <;> intro hb <;> rw [henc.pair_check] at hb <;>
      cases v <;> simp_all [Value.isPair, Value.asAtom]

theorem Spec.zf_to_bool {b : Bool} (hz : st.zf = some b)
  (h : Spec funs fuel { st with rax := if b then true_val else false_val } code Q r) :
  Spec funs fuel st (zf_to_bool ++ code) Q r :=
  by
    simp only [_root_.zf_to_bool, List.cons_append, List.nil_append]
    refine Spec.step ?_
    cases b
    · refine Spec.step (hs := by
        simp [ProcessorState.skip, processDirective, ProcessorState.setReg, hz]) ?_
      exact Spec.step h
    · exact Spec.jump (n := 1) rfl
        (by simp [ProcessorState.skip, processDirective, ProcessorState.setReg, hz]) (by simp) h

theorem Spec.cf_to_bool {b : Bool} (hc : st.cf = some b)
  (h : Spec funs fuel { st with rax := if b then true_val else false_val } code Q r) :
  Spec funs fuel st (cf_to_bool ++ code) Q r :=
  by
    simp only [_root_.cf_to_bool, List.cons_append, List.nil_append]
    refine Spec.step ?_
    cases b
    · refine Spec.step (hs := by
        simp [ProcessorState.skip, processDirective, ProcessorState.setReg, hc]) ?_
      exact Spec.step h
    · exact Spec.jump (n := 1) rfl
        (by simp [ProcessorState.skip, processDirective, ProcessorState.setReg, hc]) (by simp) h

end


/- ## The heap and the stack frame -/

-- pops the top of a stack we know the shape of
theorem pop_eq {s : ProcessorState} {v : Nat} {rest : List Nat} (h : s.stack = v :: rest)
  (r : Register) : processDirective s (Pop r) = { s.setReg v r with stack := rest } :=
  by
    simp [processDirective, ProcessorState.stackPop, h]


-- the heap only grows: the heap pointer doesn't go down, and nothing below it changes
def Grows (st st' : ProcessorState) : Prop :=
  st.r15 ≤ st'.r15 ∧ ∀ a, a < st.r15 → st'.mem a = st.mem a

theorem Grows.refl (st : ProcessorState) : Grows st st :=
  ⟨Nat.le_refl _, fun _ _ => rfl⟩

theorem Grows.trans {s₁ s₂ s₃ : ProcessorState} (h₁ : Grows s₁ s₂) (h₂ : Grows s₂ s₃) :
  Grows s₁ s₃ :=
  ⟨Nat.le_trans h₁.1 h₂.1, fun a ha => by rw [h₂.2 a (by have := h₁.1; omega), h₁.2 a ha]⟩

-- a state with the same heap
theorem Grows.same {s s' : ProcessorState} (hr15 : s'.r15 = s.r15) (hmem : s'.mem = s.mem) :
  Grows s s' :=
  ⟨by omega, fun _ _ => by rw [hmem]⟩

theorem Encodes.grow {s s' : ProcessorState} {v : Value} {w : Nat}
  (h : Encodes s.mem s.r15 v w) (hg : Grows s s') : Encodes s'.mem s'.r15 v w :=
  h.mono hg.1 hg.2

-- what the code for an expression leaves behind: its value in rax, the stack it started with,
-- and a heap that has only grown, with the heap pointer still a multiple of 8
def Post (st : ProcessorState) (v : Value) (st' : ProcessorState) : Prop :=
  Encodes st'.mem st'.r15 v st'.rax ∧ st'.stack = st.stack ∧ Grows st st' ∧ st'.r15 % 8 = 0

-- a state that only differs from `s` in its registers and flags
theorem Post.update {st s s' : ProcessorState} {v v' : Value} (h : Post st v s)
  (hstack : s'.stack = s.stack) (hmem : s'.mem = s.mem) (hr15 : s'.r15 = s.r15)
  (henc : Encodes s.mem s.r15 v' s'.rax) : Post st v' s' :=
  ⟨by rw [hmem, hr15]; exact henc, by rw [hstack, h.2.1], h.2.2.1.trans (Grows.same hr15 hmem),
   by rw [hr15]; exact h.2.2.2⟩

-- the compiler's table agrees with the interpreter's environment: they have the same
-- variables in the same order, and each variable's slot in the frame holds its value. the frame
-- is the top `depth` values on the stack
inductive Matches (mem : Nat → Nat) (hp : Nat) (stack : List Nat) (depth : Nat) :
    Env → Symtab → Prop
| nil : Matches mem hp stack depth [] []
| cons {env : Env} {tab : Symtab} {x : String} {v : Value} {i w : Nat} :
    i < depth → stack[depth - 1 - i]? = some w → Encodes mem hp v w →
    Matches mem hp stack depth env tab →
    Matches mem hp stack depth ((x, v) :: env) ((x, i) :: tab)

section
variable {mem : Nat → Nat} {hp : Nat} {stack : List Nat} {depth : Nat} {env : Env} {tab : Symtab}

theorem Matches.lookup_none (hm : Matches mem hp stack depth env tab) (x : String)
  (h : env.lookup x = none) : tab.lookup x = none :=
  by
    induction hm with
    | nil => rfl
    | @cons env tab y v i w hi hslot henc hm ih =>
      simp only [List.lookup] at h ⊢
      cases hxy : x == y
      · simp only [hxy] at h ⊢
        exact ih h
      · simp [hxy] at h

theorem Matches.lookup_some (hm : Matches mem hp stack depth env tab) (x : String) (v : Value)
  (h : env.lookup x = some v) :
  ∃ i w, tab.lookup x = some i ∧ stack[depth - 1 - i]? = some w ∧ Encodes mem hp v w :=
  by
    induction hm with
    | nil => simp [List.lookup] at h
    | @cons env tab y v' i w hi hslot henc hm ih =>
      simp only [List.lookup] at h ⊢
      cases hxy : x == y <;> simp_all

theorem Matches.grow {mem' : Nat → Nat} {hp' : Nat} (hm : Matches mem hp stack depth env tab)
  (hhp : hp ≤ hp') (hmem : ∀ a, a < hp → mem' a = mem a) :
  Matches mem' hp' stack depth env tab :=
  by
    induction hm with
    | nil => exact .nil
    | cons hi hslot henc _ ih => exact .cons hi hslot (henc.mono hhp hmem) ih

-- pushing a value adds it to the frame without moving any slots
theorem Matches.push (hm : Matches mem hp stack depth env tab) (w : Nat) :
  Matches mem hp (w :: stack) (depth + 1) env tab :=
  by
    induction hm with
    | nil => exact .nil
    | @cons env tab x v i w' hi hslot henc _ ih =>
      refine .cons (by omega) ?_ henc ih
      have : depth + 1 - 1 - i = (depth - 1 - i) + 1 := by omega
      rw [this, List.getElem?_cons_succ, hslot]

-- `Let` puts its variable in the slot it just pushed
theorem Matches.bind (hm : Matches mem hp stack depth env tab) (x : String) {v : Value} {w : Nat}
  (henc : Encodes mem hp v w) :
  Matches mem hp (w :: stack) (depth + 1) ((x, v) :: env) ((x, depth) :: tab) :=
  .cons (by omega) (by simp) henc (hm.push w)

end

-- the variables in scope are where the table says they are
def Scope (st : ProcessorState) (env : Env) (tab : Symtab) (depth : Nat) : Prop :=
  Matches st.mem st.r15 st.stack depth env tab ∧ st.r15 % 8 = 0

-- after running some code that leaves the stack alone
theorem Scope.after {st s : ProcessorState} {env : Env} {tab : Symtab} {depth : Nat}
  (hinv : Scope st env tab depth) (hstack : s.stack = st.stack) (hg : Grows st s)
  (halign : s.r15 % 8 = 0) : Scope s env tab depth :=
  ⟨by rw [hstack]; exact hinv.1.grow hg.1 hg.2, halign⟩

-- after running some code and pushing a value
theorem Scope.push {st s : ProcessorState} {env : Env} {tab : Symtab} {depth : Nat} {w : Nat}
  (hinv : Scope st env tab depth) (hstack : s.stack = w :: st.stack) (hg : Grows st s)
  (halign : s.r15 % 8 = 0) : Scope s env tab (depth + 1) :=
  ⟨by rw [hstack]; exact (hinv.1.grow hg.1 hg.2).push w, halign⟩

-- the values of a list of arguments
inductive ArgsEnc (mem : Nat → Nat) (hp : Nat) : List Value → List Nat → Prop
| nil : ArgsEnc mem hp [] []
| cons {v : Value} {vs : List Value} {w : Nat} {ws : List Nat} :
    Encodes mem hp v w → ArgsEnc mem hp vs ws → ArgsEnc mem hp (v :: vs) (w :: ws)

theorem ArgsEnc.mono {mem mem' : Nat → Nat} {hp hp' : Nat} {vs : List Value} {ws : List Nat}
  (h : ArgsEnc mem hp vs ws) (hhp : hp ≤ hp') (hmem : ∀ a, a < hp → mem' a = mem a) :
  ArgsEnc mem' hp' vs ws :=
  by
    induction h with
    | nil => exact .nil
    | cons henc _ ih => exact .cons (henc.mono hhp hmem) ih

theorem ArgsEnc.length_eq {mem : Nat → Nat} {hp : Nat} {vs : List Value} {ws : List Nat}
  (h : ArgsEnc mem hp vs ws) : vs.length = ws.length :=
  by
    induction h with
    | nil => rfl
    | cons _ _ ih => simp [ih]

-- the parameters of a function, `k` slots up from the bottom of the frame
theorem Matches.params {mem : Nat → Nat} {hp : Nat} {stack : List Nat} {depth : Nat} :
  ∀ (ps : List String) (vs : List Value) (ws : List Nat) (k : Nat),
    ps.length = vs.length → ArgsEnc mem hp vs ws →
    (∀ j (hj : j < ws.length), k + j < depth ∧ stack[depth - 1 - (k + j)]? = some ws[j]) →
    Matches mem hp stack depth (ps.zip vs) (ps.zipIdx k)
  | [], _, _, _, _, _, _ => by simp; exact .nil
  | p :: ps, v :: vs, w :: ws, k, hlen, .cons henc hargs, hslots =>
    by
      simp only [List.zip_cons_cons, List.zipIdx_cons]
      have h0 := hslots 0 (by simp)
      simp only [Nat.add_zero, List.getElem_cons_zero] at h0
      refine .cons h0.1 h0.2 henc (Matches.params ps vs ws (k + 1) (by simpa using hlen) hargs ?_)
      intro j hj
      have := hslots (j + 1) (by simp; omega)
      simp only [List.getElem_cons_succ] at this
      rw [show k + 1 + j = k + (j + 1) by omega]
      exact this
  | _ :: _, [], _, _, hlen, _, _ => by simp at hlen

-- when a function starts, its arguments are under the return address
theorem Matches.entry {mem : Nat → Nat} {hp : Nat} (ps : List String) (vs : List Value)
  (ws below : List Nat) (hlen : ps.length = vs.length) (hargs : ArgsEnc mem hp vs ws) :
  Matches mem hp (0 :: (ws.reverse ++ below)) (ws.length + 1) (ps.zip vs) (param_tab ps) :=
  by
    apply Matches.params ps vs ws 0 hlen hargs
    intro j hj
    refine ⟨by omega, ?_⟩
    have : ws.length + 1 - 1 - (0 + j) = (ws.length - 1 - j) + 1 := by omega
    rw [this, List.getElem?_cons_succ, List.getElem?_append_left (by simp; omega),
      List.getElem?_reverse (by omega)]
    simp only [List.getElem?_eq_getElem (show ws.length - 1 - (ws.length - 1 - j) < ws.length by omega)]
    congr 2
    omega



-- a state with the same stack and heap as one that an expression's code left behind
theorem Post.chain {st s₁ c s : ProcessorState} {v₁ v : Value} (h₁ : Post st v₁ s₁)
  (hstack : c.stack = s₁.stack) (hmem : c.mem = s₁.mem) (hr15 : c.r15 = s₁.r15)
  (h : Post c v s) : Post st v s :=
  ⟨h.1, by rw [h.2.1, hstack, h₁.2.1], h₁.2.2.1.trans ((Grows.same hr15 hmem).trans h.2.2.1),
   h.2.2.2⟩

theorem Scope.of_post {st s₁ c : ProcessorState} {v₁ : Value} {env : Env} {tab : Symtab}
  {depth : Nat} (hsc : Scope st env tab depth) (h₁ : Post st v₁ s₁)
  (hstack : c.stack = s₁.stack) (hmem : c.mem = s₁.mem) (hr15 : c.r15 = s₁.r15) :
  Scope c env tab depth :=
  hsc.after (by rw [hstack, h₁.2.1]) (h₁.2.2.1.trans (Grows.same hr15 hmem))
    (by rw [hr15]; exact h₁.2.2.2)

-- pushing the value that an expression's code left in rax
theorem Scope.push_post {st s₁ : ProcessorState} {v₁ : Value} {env : Env} {tab : Symtab}
  {depth : Nat} (hsc : Scope st env tab depth) (h₁ : Post st v₁ s₁) :
  Scope (processDirective s₁ (Push (Reg Rax))) env tab (depth + 1) :=
  hsc.push (w := s₁.rax) (by simp [processDirective, ProcessorState.stackPush,
    ProcessorState.opVal, ProcessorState.regVal, h₁.2.1]) (h₁.2.2.1.trans (Grows.same rfl rfl))
    h₁.2.2.2

-- the tag checks only touch r8 and the flags
theorem Post.checked {st s : ProcessorState} {v : Value} (h : Post st v s) (mask tag : Nat) :
  Post st v (checked s mask tag) :=
  h.update rfl rfl rfl h.1

-- after pushing the value in rax and running more code that leaves the stack alone, the value
-- is back on top
theorem Post.pushed_stack {s s₂ : ProcessorState} {v : Value}
  (h : Post (processDirective s (Push (Reg Rax))) v s₂) : s₂.stack = s.rax :: s.stack :=
  h.2.1

theorem Post.pushed_grows {st s₁ s₂ : ProcessorState} {v₁ v₂ : Value} (h₁ : Post st v₁ s₁)
  (h₂ : Post (processDirective s₁ (Push (Reg Rax))) v₂ s₂) : Grows st s₂ :=
  h₁.2.2.1.trans ((Grows.same rfl rfl).trans h₂.2.2.1)

/- ## Calls -/

-- what running a function's code does, when its answer should be `r`
def Returns (funs : List (String × List Directive)) (fuel : Nat) {α : Type} (st : ProcessorState)
    (code : List Directive) (P : α → ProcessorState → Prop) : Outcome α → Prop
| .done a => ∃ st', Processor.run funs fuel st code = .done st' ∧ P a st'
| .error => Processor.run funs fuel st code = .error
| .timeout => Processor.run funs fuel st code = .timeout

section
variable {funs : List (String × List Directive)} {fuel : Nat} {α β : Type} {st : ProcessorState}
  {code : List Directive} {P : α → ProcessorState → Prop} {Q : β → ProcessorState → Prop}
  {r : Outcome α}

-- a function body is its expression's code followed by `Ret`
theorem Spec.ret (h : Spec funs fuel st code P r) :
  Returns funs fuel st (code ++ [Ret])
    (fun a s' => ∃ s, P a s ∧ s' = { s with stack := s.stack.drop 1 }) r :=
  by
    cases r with
    | done a =>
      obtain ⟨s, hrun, hs⟩ := h
      exact ⟨_, by rw [hrun]; simp, s, hs, rfl⟩
    | error => exact h [Ret]
    | timeout => exact h [Ret]

theorem Spec.call {f : String} {body : List Directive} {r : Outcome β}
  {R : β → ProcessorState → Prop} (hf : funs.lookup f = some body)
  (h : Returns funs fuel (st.stackPush 0) body R r)
  (hk : ∀ a s, R a s → Spec funs (fuel + 1) s code Q (.done a)) :
  Spec funs (fuel + 1) st (Call f :: code) Q r :=
  by
    cases r with
    | done a =>
      obtain ⟨s, hrun, hs⟩ := h
      obtain ⟨s', hrun', hs'⟩ := hk a s hs
      refine ⟨s', fun rest => ?_, hs'⟩
      rw [List.cons_append, Processor.run_call, hf]
      simp only [hrun]
      exact hrun' rest
    | error =>
      intro rest
      have h' : Processor.run funs fuel (st.stackPush 0) body = .error := h
      rw [List.cons_append, Processor.run_call, hf]
      simp only [h']
    | timeout =>
      intro rest
      have h' : Processor.run funs fuel (st.stackPush 0) body = .timeout := h
      rw [List.cons_append, Processor.run_call, hf]
      simp only [h']

theorem Spec.call_zero {f : String} : Spec funs 0 st (Call f :: code) Q .timeout :=
  by
    intro rest
    rw [List.cons_append, Processor.run_call_zero]

theorem Returns.mono {P' : α → ProcessorState → Prop} (h : Returns funs fuel st code P r)
  (hP : ∀ a s, P a s → P' a s) : Returns funs fuel st code P' r :=
  by
    cases r with
    | done a =>
      obtain ⟨s, hrun, hs⟩ := h
      exact ⟨s, hrun, hP a s hs⟩
    | error => exact h
    | timeout => exact h

-- the code that puts a pair on the heap, with its first half on the stack and its second half
-- in rax
theorem Spec.alloc {w₁ : Nat} {below : List Nat} {r : Outcome β} (hstack : st.stack = w₁ :: below)
  (h : Spec funs fuel
    { st with rax := st.r15 + pair_tag, rcx := w₁, r15 := st.r15 + 16, stack := below,
              mem := fun a => if a = st.r15 + 8 then st.rax else if a = st.r15 then w₁ else st.mem a,
              zf := none, cf := none } code Q r) :
  Spec funs fuel st
    (Pop Rcx :: StoreMem R15 0 Rcx :: StoreMem R15 8 Rax :: Mov (Reg Rax, Reg R15) ::
      Directive.Add (Reg Rax, Imm pair_tag) :: Directive.Add (Reg R15, Imm 16) :: code) Q r :=
  by
    refine Spec.step ?_
    rw [pop_eq hstack]
    exact Spec.step (Spec.step (Spec.step (Spec.step (Spec.step h))))

end


/- ## Correctness -/

theorem lookup_map_findDef {β : Type} (g : Defn → β) (f : String) :
  ∀ defs : List Defn, (defs.map (fun d => (d.name, g d))).lookup f = (findDef f defs).map g
  | [] => rfl
  | d :: ds =>
    by
      simp only [List.map_cons, List.lookup, findDef]
      by_cases h : d.name = f
      · simp [h]
      · have hb : (f == d.name) = false := by simpa using fun h' => h h'.symm
        simp [hb, h, lookup_map_findDef g f ds]

section
variable (defs : List Defn)

-- the compiled functions
def funs_of : List (String × List Directive) :=
  defs.map (fun d => (d.name, compile_defn (sigs_of defs) d))

-- calling a function, with `fuel` left for the calls it makes, does what the interpreter does
def CallsOk (fuel : Nat) : Prop :=
  ∀ f d, findDef f defs = some d →
  ∀ (st : ProcessorState) (vs : List Value) (ws below : List Nat),
    st.stack = 0 :: (ws.reverse ++ below) → ArgsEnc st.mem st.r15 vs ws →
    d.params.length = vs.length → st.r15 % 8 = 0 →
    Returns (funs_of defs) fuel st (compile_defn (sigs_of defs) d)
      (fun v st' => Encodes st'.mem st'.r15 v st'.rax ∧ st'.stack = ws.reverse ++ below ∧
        Grows st st' ∧ st'.r15 % 8 = 0)
      (interp defs fuel (d.params.zip vs) d.body)

-- what the code for a list of `len` arguments leaves behind: their values pushed onto the stack
def PostArgs (len : Nat) (st : ProcessorState) (vs : List Value) (st' : ProcessorState) : Prop :=
  ∃ ws, st'.stack = ws.reverse ++ st.stack ∧ ArgsEnc st'.mem st'.r15 vs ws ∧ Grows st st' ∧
    st'.r15 % 8 = 0 ∧ vs.length = len

-- skipping over some code and a jump
theorem drop_past {γ : Type} (a b : List γ) (x : γ) : (a ++ x :: b).drop (a.length + 1) = b :=
  by
    simp

mutual
-- the compiled code for `e` does what the interpreter does, from any state whose stack frame
-- has the variables in `env` where `tab` says. the code for a function call runs the function
-- with one less unit of fuel, so this only needs calls to work with less fuel than `n`
theorem compile_expr_spec (n : Nat) (hcalls : ∀ m < n, CallsOk defs m) :
  ∀ (e : Expr) (env : Env) (tab : Symtab) (depth : Nat) (st : ProcessorState),
    Scope st env tab depth →
    Spec (funs_of defs) n st (compile_expr (sigs_of defs) tab depth e) (Post st)
      (interp defs n env e)
  | Num k, env, tab, depth, st, hsc =>
    by
      simp only [interp, compile_expr]
      exact Spec.step (Spec.pure ⟨Encodes.int' rfl, rfl, Grows.same rfl rfl, hsc.2⟩)

  | Expr.Bool b, env, tab, depth, st, hsc =>
    by
      simp only [interp, compile_expr]
      cases b
      · exact Spec.step (Spec.pure ⟨Encodes.bool' rfl, rfl, Grows.same rfl rfl, hsc.2⟩)
      · exact Spec.step (Spec.pure ⟨Encodes.bool' rfl, rfl, Grows.same rfl rfl, hsc.2⟩)

  | Add1 e, env, tab, depth, st, hsc =>
    by
      simp only [interp, compile_expr, List.append_assoc]
      refine Spec.bind (compile_expr_spec n hcalls e env tab depth st hsc) fun v s₁ h₁ => ?_
      refine Spec.ensure_num h₁.1 fun i hv => ?_
      subst hv
      refine Spec.step (Spec.pure (h₁.update rfl rfl rfl (Encodes.int' ?_)))
      simp [processDirective, ProcessorState.setReg, ProcessorState.regVal, ProcessorState.opVal,
        checked, h₁.1.int_inv, num_shift, Nat.shiftLeft_eq]
      omega

  | Sub1 e, env, tab, depth, st, hsc =>
    by
      simp only [interp, compile_expr, List.append_assoc]
      refine Spec.bind (compile_expr_spec n hcalls e env tab depth st hsc) fun v s₁ h₁ => ?_
      refine Spec.ensure_num h₁.1 fun i hv => ?_
      subst hv
      refine Spec.step (Spec.pure (h₁.update rfl rfl rfl (Encodes.int' ?_)))
      simp [processDirective, ProcessorState.setReg, ProcessorState.regVal, ProcessorState.opVal,
        checked, h₁.1.int_inv, num_shift, Nat.shiftLeft_eq]
      omega

  -- run e₁ and check it, push it, run e₂ and check it, pop e₁'s value into rcx, then add
  | Expr.Add e₁ e₂, env, tab, depth, st, hsc =>
    by
      simp only [interp, compile_expr, List.append_assoc, List.cons_append, List.nil_append]
      refine Spec.bind (compile_expr_spec n hcalls e₁ env tab depth st hsc) fun v₁ s₁ h₁ => ?_
      refine Spec.ensure_num h₁.1 fun i₁ hv₁ => ?_
      subst hv₁
      have h₁' := h₁.checked num_mask num_tag
      refine Spec.step ?_
      refine Spec.bind (compile_expr_spec n hcalls e₂ env tab (depth + 1) _ (hsc.push_post h₁'))
        fun v₂ s₂ h₂ => ?_
      refine Spec.ensure_num h₂.1 fun i₂ hv₂ => ?_
      subst hv₂
      refine Spec.step ?_
      rw [pop_eq (show (checked s₂ num_mask num_tag).stack = s₁.rax :: st.stack by
        simp [checked, h₂.pushed_stack, h₁.2.1])]
      refine Spec.step (Spec.pure ⟨Encodes.int' ?_, rfl, ?_, h₂.2.2.2⟩)
      · simp [processDirective, ProcessorState.setReg, ProcessorState.regVal, ProcessorState.opVal,
          checked, h₁.1.int_inv, h₂.1.int_inv, num_shift, Nat.shiftLeft_eq]
        omega
      · exact (h₁'.pushed_grows h₂).trans (Grows.same rfl rfl)

  | Expr.Sub e₁ e₂, env, tab, depth, st, hsc =>
    by
      simp only [interp, compile_expr, List.append_assoc, List.cons_append, List.nil_append]
      refine Spec.bind (compile_expr_spec n hcalls e₁ env tab depth st hsc) fun v₁ s₁ h₁ => ?_
      refine Spec.ensure_num h₁.1 fun i₁ hv₁ => ?_
      subst hv₁
      have h₁' := h₁.checked num_mask num_tag
      refine Spec.step ?_
      refine Spec.bind (compile_expr_spec n hcalls e₂ env tab (depth + 1) _ (hsc.push_post h₁'))
        fun v₂ s₂ h₂ => ?_
      refine Spec.ensure_num h₂.1 fun i₂ hv₂ => ?_
      subst hv₂
      refine Spec.step ?_
      rw [pop_eq (show (checked s₂ num_mask num_tag).stack = s₁.rax :: st.stack by
        simp [checked, h₂.pushed_stack, h₁.2.1])]
      refine Spec.step (Spec.step (Spec.pure ⟨Encodes.int' ?_, rfl, ?_, h₂.2.2.2⟩))
      · simp [processDirective, ProcessorState.setReg, ProcessorState.regVal, ProcessorState.opVal,
          checked, h₁.1.int_inv, h₂.1.int_inv, num_shift, Nat.shiftLeft_eq]
        omega
      · exact (h₁'.pushed_grows h₂).trans (Grows.same rfl rfl)

  | IsZero e, env, tab, depth, st, hsc =>
    by
      simp only [interp, compile_expr, List.append_assoc, List.cons_append, List.nil_append]
      refine Spec.bind (compile_expr_spec n hcalls e env tab depth st hsc) fun v s₁ h₁ => ?_
      refine Spec.ensure_num h₁.1 fun i hv => ?_
      subst hv
      refine Spec.step (Spec.zf_to_bool (b := decide (i = 0)) ?_
        (Spec.pure (h₁.update rfl rfl rfl (Encodes.bool' rfl))))
      simp [processDirective, ProcessorState.opVal, ProcessorState.regVal, checked,
        h₁.1.int_inv, num_shift, Nat.shiftLeft_eq]
      cases i <;> simp

  | Lt e₁ e₂, env, tab, depth, st, hsc =>
    by
      simp only [interp, compile_expr, List.append_assoc, List.cons_append, List.nil_append]
      refine Spec.bind (compile_expr_spec n hcalls e₁ env tab depth st hsc) fun v₁ s₁ h₁ => ?_
      refine Spec.ensure_num h₁.1 fun i₁ hv₁ => ?_
      subst hv₁
      have h₁' := h₁.checked num_mask num_tag
      refine Spec.step ?_
      refine Spec.bind (compile_expr_spec n hcalls e₂ env tab (depth + 1) _ (hsc.push_post h₁'))
        fun v₂ s₂ h₂ => ?_
      refine Spec.ensure_num h₂.1 fun i₂ hv₂ => ?_
      subst hv₂
      refine Spec.step ?_
      rw [pop_eq (show (checked s₂ num_mask num_tag).stack = s₁.rax :: st.stack by
        simp [checked, h₂.pushed_stack, h₁.2.1])]
      refine Spec.step (Spec.cf_to_bool (b := decide (i₁ < i₂)) ?_
        (Spec.pure ⟨Encodes.bool' rfl, rfl, ?_, h₂.2.2.2⟩))
      · simp [processDirective, ProcessorState.setReg, ProcessorState.regVal, ProcessorState.opVal,
          checked, h₁.1.int_inv, h₂.1.int_inv, num_shift, Nat.shiftLeft_eq]
      · exact (h₁'.pushed_grows h₂).trans (Grows.same rfl rfl)

  | If c t f, env, tab, depth, st, hsc =>
    by
      simp only [interp, compile_expr, List.append_assoc, List.cons_append, List.nil_append]
      refine Spec.bind (compile_expr_spec n hcalls c env tab depth st hsc) fun v s₁ h₁ => ?_
      refine Spec.ensure_bool h₁.1 fun b hv => ?_
      subst hv
      -- compare c's value against false
      refine Spec.step ?_
      have hsc' := hsc.of_post (c := processDirective (checked s₁ bool_mask bool_tag)
        (Cmp (Reg Rax, Imm false_val))) h₁ rfl rfl rfl
      cases b
      · -- c is false: the `Je` skips over t and the `Jmp`, straight to f
        refine Spec.jump (n := (compile_expr (sigs_of defs) tab depth t).length + 1) rfl (by simp [ProcessorState.skip, processDirective, ProcessorState.opVal,
          ProcessorState.regVal, checked, h₁.1.bool_inv]) (by simp) ?_
        rw [drop_past]
        exact (compile_expr_spec n hcalls f env tab depth _ hsc').mono
          fun v s h => h₁.chain rfl rfl rfl h
      · -- c is true: the `Je` falls through into t, then the `Jmp` skips over f
        refine Spec.step (hs := by simp [ProcessorState.skip, processDirective,
          ProcessorState.opVal, ProcessorState.regVal, checked, h₁.1.bool_inv, true_val,
          false_val, bool_shift, bool_tag]) ?_
        refine Spec.then (compile_expr_spec n hcalls t env tab depth _ hsc') fun v s h => ?_
        refine Spec.jump rfl rfl (Nat.le_refl _) ?_
        rw [List.drop_length]
        exact Spec.pure (h₁.chain rfl rfl rfl h)

  | Expr.Not e, env, tab, depth, st, hsc =>
    by
      simp only [interp, compile_expr, List.append_assoc, List.cons_append, List.nil_append]
      refine Spec.bind (compile_expr_spec n hcalls e env tab depth st hsc) fun v s₁ h₁ => ?_
      refine Spec.ensure_bool h₁.1 fun b hv => ?_
      subst hv
      -- the value is equal to false exactly when its negation is true
      refine Spec.step (Spec.zf_to_bool (b := !b) ?_
        (Spec.pure (h₁.update rfl rfl rfl (Encodes.bool' rfl))))
      cases b <;> simp [processDirective, ProcessorState.opVal, ProcessorState.regVal, checked,
        h₁.1.bool_inv, true_val, false_val, bool_shift, bool_tag]

  | Expr.Eq e₁ e₂, env, tab, depth, st, hsc =>
    by
      simp only [interp, compile_expr, List.append_assoc, List.cons_append, List.nil_append]
      refine Spec.bind (compile_expr_spec n hcalls e₁ env tab depth st hsc) fun v₁ s₁ h₁ => ?_
      refine Spec.ensure_atom h₁.1 fun ha₁ => ?_
      have h₁' := h₁.checked heap_mask pair_tag
      refine Spec.step ?_
      refine Spec.bind (compile_expr_spec n hcalls e₂ env tab (depth + 1) _ (hsc.push_post h₁'))
        fun v₂ s₂ h₂ => ?_
      refine Spec.ensure_atom h₂.1 fun ha₂ => ?_
      refine Spec.step ?_
      rw [pop_eq (show (checked s₂ heap_mask pair_tag).stack = s₁.rax :: st.stack by
        simp [checked, h₂.pushed_stack, h₁.2.1])]
      -- compare the two encodings
      refine Spec.step (Spec.zf_to_bool (b := decide (v₁ = v₂)) ?_
        (Spec.pure ⟨Encodes.bool' rfl, rfl, ?_, h₂.2.2.2⟩))
      · simp only [processDirective, ProcessorState.setReg, ProcessorState.opVal,
          ProcessorState.regVal, checked]
        rw [h₁.1.eq_check h₂.1 ha₁ ha₂]
      · exact (h₁'.pushed_grows h₂).trans (Grows.same rfl rfl)

  | Expr.And e₁ e₂, env, tab, depth, st, hsc =>
    by
      simp only [interp, compile_expr, List.append_assoc, List.cons_append, List.nil_append]
      refine Spec.bind (compile_expr_spec n hcalls e₁ env tab depth st hsc) fun v s₁ h₁ => ?_
      refine Spec.ensure_bool h₁.1 fun b hv => ?_
      subst hv
      refine Spec.step ?_
      have hsc' := hsc.of_post (c := processDirective (checked s₁ bool_mask bool_tag)
        (Cmp (Reg Rax, Imm false_val))) h₁ rfl rfl rfl
      cases b
      · -- e₁ is false, so that's the answer: the `Je` skips over e₂ and rax still holds false
        refine Spec.jump rfl (by simp [ProcessorState.skip, processDirective, ProcessorState.opVal,
          ProcessorState.regVal, checked, h₁.1.bool_inv]) (Nat.le_refl _) ?_
        rw [List.drop_length]
        exact Spec.pure (h₁.update rfl rfl rfl h₁.1)
      · -- e₁ is true, so the answer is whatever e₂ is
        refine Spec.step (hs := by simp [ProcessorState.skip, processDirective,
          ProcessorState.opVal, ProcessorState.regVal, checked, h₁.1.bool_inv, true_val,
          false_val, bool_shift, bool_tag]) ?_
        rw [← List.append_nil ensure_bool]
        refine Spec.bind (compile_expr_spec n hcalls e₂ env tab depth _ hsc') fun v₂ s₂ h₂ => ?_
        refine Spec.ensure_bool h₂.1 fun b₂ hv₂ => ?_
        subst hv₂
        exact Spec.pure (h₁.chain rfl rfl rfl (h₂.checked bool_mask bool_tag))

  | Expr.Or e₁ e₂, env, tab, depth, st, hsc =>
    by
      simp only [interp, compile_expr, List.append_assoc, List.cons_append, List.nil_append]
      refine Spec.bind (compile_expr_spec n hcalls e₁ env tab depth st hsc) fun v s₁ h₁ => ?_
      refine Spec.ensure_bool h₁.1 fun b hv => ?_
      subst hv
      refine Spec.step ?_
      have hsc' := hsc.of_post (c := processDirective (checked s₁ bool_mask bool_tag)
        (Cmp (Reg Rax, Imm true_val))) h₁ rfl rfl rfl
      cases b
      · -- e₁ is false, so the answer is whatever e₂ is
        refine Spec.step (hs := by simp [ProcessorState.skip, processDirective,
          ProcessorState.opVal, ProcessorState.regVal, checked, h₁.1.bool_inv, true_val,
          false_val, bool_shift, bool_tag]) ?_
        rw [← List.append_nil ensure_bool]
        refine Spec.bind (compile_expr_spec n hcalls e₂ env tab depth _ hsc') fun v₂ s₂ h₂ => ?_
        refine Spec.ensure_bool h₂.1 fun b₂ hv₂ => ?_
        subst hv₂
        exact Spec.pure (h₁.chain rfl rfl rfl (h₂.checked bool_mask bool_tag))
      · -- e₁ is true, so that's the answer: the `Je` skips over e₂ and rax still holds true
        refine Spec.jump rfl (by simp [ProcessorState.skip, processDirective, ProcessorState.opVal,
          ProcessorState.regVal, checked, h₁.1.bool_inv]) (Nat.le_refl _) ?_
        rw [List.drop_length]
        exact Spec.pure (h₁.update rfl rfl rfl h₁.1)

  -- `num?`, `bool?` and `pair?` run the same tag test as the checks, but put the answer in rax
  | IsNum e, env, tab, depth, st, hsc =>
    by
      simp only [interp, compile_expr, List.append_assoc]
      refine Spec.bind (compile_expr_spec n hcalls e env tab depth st hsc) fun v s₁ h₁ => ?_
      refine Spec.tag_test (Spec.zf_to_bool (b := v.isNum) ?_
        (Spec.pure (h₁.update rfl rfl rfl (Encodes.bool' rfl))))
      simp only [checked]
      rw [h₁.1.num_check]

  | IsBool e, env, tab, depth, st, hsc =>
    by
      simp only [interp, compile_expr, List.append_assoc]
      refine Spec.bind (compile_expr_spec n hcalls e env tab depth st hsc) fun v s₁ h₁ => ?_
      refine Spec.tag_test (Spec.zf_to_bool (b := v.isBool) ?_
        (Spec.pure (h₁.update rfl rfl rfl (Encodes.bool' rfl))))
      simp only [checked]
      rw [h₁.1.bool_check]

  | IsPair e, env, tab, depth, st, hsc =>
    by
      simp only [interp, compile_expr, List.append_assoc]
      refine Spec.bind (compile_expr_spec n hcalls e env tab depth st hsc) fun v s₁ h₁ => ?_
      refine Spec.tag_test (Spec.zf_to_bool (b := v.isPair) ?_
        (Spec.pure (h₁.update rfl rfl rfl (Encodes.bool' rfl))))
      simp only [checked]
      rw [h₁.1.pair_check]

  | Var x, env, tab, depth, st, hsc =>
    by
      simp only [interp, compile_expr]
      cases hv : env.lookup x with
      | none =>
        -- not in scope for the interpreter, so not in the compiler's table either
        rw [hsc.1.lookup_none x hv]
        exact Spec.error_here
      | some v =>
        obtain ⟨i, w, hi, hslot, henc⟩ := hsc.1.lookup_some x v hv
        rw [hi]
        refine Spec.step (Spec.pure ⟨?_, rfl, Grows.same rfl rfl, hsc.2⟩)
        simp only [processDirective, List.getD_eq_getElem?_getD, hslot, Option.getD_some]
        exact henc

  | Let x e body, env, tab, depth, st, hsc =>
    by
      simp only [interp, compile_expr, List.append_assoc, List.cons_append, List.nil_append]
      refine Spec.bind (compile_expr_spec n hcalls e env tab depth st hsc) fun v s₁ h₁ => ?_
      -- push e's value, so it's in slot `depth` while the body runs
      refine Spec.step ?_
      have hpush : (processDirective s₁ (Push (Reg Rax))).stack = s₁.rax :: st.stack :=
        by
          simp [processDirective, ProcessorState.stackPush, ProcessorState.opVal,
            ProcessorState.regVal, h₁.2.1]
      have hsc' : Scope (processDirective s₁ (Push (Reg Rax))) ((x, v) :: env) ((x, depth) :: tab)
          (depth + 1) :=
        ⟨by rw [hpush]; exact (hsc.1.grow h₁.2.2.1.1 h₁.2.2.1.2).bind x h₁.1, h₁.2.2.2⟩
      refine Spec.then (compile_expr_spec n hcalls body _ _ _ _ hsc') fun w s₂ h₂ => ?_
      -- pop the slot back off, which leaves the body's value in rax
      refine Spec.step ?_
      rw [pop_eq (h₂.2.1.trans hpush)]
      exact Spec.pure ⟨h₂.1, rfl, (h₁.pushed_grows h₂).trans (Grows.same rfl rfl), h₂.2.2.2⟩

  | Expr.Pair e₁ e₂, env, tab, depth, st, hsc =>
    by
      simp only [interp, compile_expr, List.append_assoc, List.cons_append, List.nil_append]
      refine Spec.bind (compile_expr_spec n hcalls e₁ env tab depth st hsc) fun v₁ s₁ h₁ => ?_
      refine Spec.step ?_
      refine Spec.bind (compile_expr_spec n hcalls e₂ env tab (depth + 1) _ (hsc.push_post h₁))
        fun v₂ s₂ h₂ => ?_
      have hg := h₁.pushed_grows h₂
      have hg₁ : s₁.r15 ≤ s₂.r15 := h₂.2.2.1.1
      have hmem₁ : ∀ a, a < s₁.r15 → s₂.mem a = s₁.mem a := h₂.2.2.1.2
      refine Spec.alloc (w₁ := s₁.rax) (below := st.stack) (by rw [h₂.pushed_stack, h₁.2.1])
        (Spec.pure ⟨?_, rfl, ⟨?_, ?_⟩, ?_⟩)
      · -- the pair's halves are below the heap pointer, and nothing else moved
        refine Encodes.pair h₂.2.2.2 (Nat.le_refl _) ?_ ?_
        · simp only [show s₂.r15 ≠ s₂.r15 + 8 by omega, ite_false, ite_true]
          exact h₁.1.mono hg₁ fun a ha => by
            simp only [show a ≠ s₂.r15 + 8 by omega, show a ≠ s₂.r15 by omega, ite_false]
            exact hmem₁ a ha
        · simp only [ite_true]
          exact h₂.1.mono (Nat.le_refl _) fun a ha => by
            simp only [show a ≠ s₂.r15 + 8 by omega, show a ≠ s₂.r15 by omega, ite_false]
      · have := hg.1
        dsimp only
        omega
      · intro a ha
        have := hg.1
        simp only [show a ≠ s₂.r15 + 8 by omega, show a ≠ s₂.r15 by omega, ite_false]
        exact hg.2 a ha
      · have := h₂.2.2.2
        dsimp only
        omega

  | Left e, env, tab, depth, st, hsc =>
    by
      simp only [interp, compile_expr, List.append_assoc]
      refine Spec.bind (compile_expr_spec n hcalls e env tab depth st hsc) fun v s₁ h₁ => ?_
      refine Spec.ensure_pair h₁.1 fun v₁ v₂ hv => ?_
      subst hv
      obtain ⟨a, ha, ha8, hle, h₁₁, h₁₂⟩ := h₁.1.pair_inv
      -- untag the pointer, then load the first half
      refine Spec.step (Spec.step (Spec.pure (h₁.update rfl rfl rfl ?_)))
      simp only [processDirective, ProcessorState.setReg, ProcessorState.regVal,
        ProcessorState.opVal, checked, ha, Nat.add_sub_cancel, Nat.add_zero]
      exact h₁₁.mono (by omega) fun _ _ => rfl

  | Right e, env, tab, depth, st, hsc =>
    by
      simp only [interp, compile_expr, List.append_assoc]
      refine Spec.bind (compile_expr_spec n hcalls e env tab depth st hsc) fun v s₁ h₁ => ?_
      refine Spec.ensure_pair h₁.1 fun v₁ v₂ hv => ?_
      subst hv
      obtain ⟨a, ha, ha8, hle, h₁₁, h₁₂⟩ := h₁.1.pair_inv
      refine Spec.step (Spec.step (Spec.pure (h₁.update rfl rfl rfl ?_)))
      simp only [processDirective, ProcessorState.setReg, ProcessorState.regVal,
        ProcessorState.opVal, checked, ha, Nat.add_sub_cancel]
      exact h₁₂.mono (by omega) fun _ _ => rfl

  -- push the arguments, call the function (which uses up one unit of fuel), then drop them
  | App f args, env, tab, depth, st, hsc =>
    by
      simp only [interp, compile_expr, sigs_of]
      rw [lookup_map_findDef (fun d => d.params.length) f defs]
      cases hd : findDef f defs with
      | none => exact Spec.error_here
      | some d =>
        dsimp only [Option.map]
        by_cases hlen : args.length = d.params.length
        · simp only [hlen, ↓reduceIte]
          refine Spec.bind (compile_args_spec n hcalls args env tab depth st hsc)
            fun vs s₁ h₁ => ?_
          obtain ⟨ws, hws, hargs, hg, halign, hvs⟩ := h₁
          cases n with
          | zero => exact Spec.call_zero
          | succ m =>
            have hlook : (funs_of defs).lookup f = some (compile_defn (sigs_of defs) d) :=
              by
                rw [funs_of, lookup_map_findDef, hd]
                rfl
            refine Spec.call hlook (hcalls m (by omega) f d hd (s₁.stackPush 0) vs ws st.stack
              (by simp [ProcessorState.stackPush, hws]) hargs (by omega) halign) fun v s₂ h₂ => ?_
            obtain ⟨henc, hstack, hg₂, halign₂⟩ := h₂
            refine Spec.step (Spec.pure ⟨henc, ?_, ?_, halign₂⟩)
            · have hk : d.params.length = ws.reverse.length := by simp [← hargs.length_eq]; omega
              simp only [processDirective, hstack, hk, List.drop_left]
            · exact hg.trans ((Grows.same rfl rfl).trans (hg₂.trans (Grows.same rfl rfl)))
        · simp only [hlen, ↓reduceIte]
          exact Spec.error_here

theorem compile_args_spec (n : Nat) (hcalls : ∀ m < n, CallsOk defs m) :
  ∀ (args : List Expr) (env : Env) (tab : Symtab) (depth : Nat) (st : ProcessorState),
    Scope st env tab depth →
    Spec (funs_of defs) n st (compile_args (sigs_of defs) tab depth args)
      (PostArgs args.length st) (interpArgs defs n env args)
  | [], env, tab, depth, st, hsc =>
    by
      simp only [interpArgs, compile_args]
      exact Spec.pure ⟨[], by simp, .nil, Grows.refl st, hsc.2, rfl⟩
  | e :: es, env, tab, depth, st, hsc =>
    by
      simp only [interpArgs, compile_args, List.append_assoc, List.cons_append, List.nil_append]
      refine Spec.bind (compile_expr_spec n hcalls e env tab depth st hsc) fun v s₁ h₁ => ?_
      refine Spec.step ?_
      rw [← List.append_nil (compile_args (sigs_of defs) tab (depth + 1) es)]
      refine Spec.bind (compile_args_spec n hcalls es env tab (depth + 1) _ (hsc.push_post h₁))
        fun vs s₂ h₂ => ?_
      obtain ⟨ws, hws, hargs, hg, halign, hlen⟩ := h₂
      refine Spec.pure ⟨s₁.rax :: ws, ?_, .cons (Encodes.grow (s := processDirective s₁
        (Push (Reg Rax))) h₁.1 hg) hargs, h₁.2.2.1.trans ((Grows.same rfl rfl).trans hg), halign,
        by simp [hlen]⟩
      simp [hws, processDirective, ProcessorState.stackPush, ProcessorState.opVal,
        ProcessorState.regVal, h₁.2.1]
end

theorem calls_ok_of_spec (n : Nat) (hcalls : ∀ m < n, CallsOk defs m) : CallsOk defs n :=
  by
    intro f d hd st vs ws below hstack hargs hlen halign
    have hws : d.params.length = ws.length := hlen.trans hargs.length_eq
    have hsc : Scope st (d.params.zip vs) (param_tab d.params) (d.params.length + 1) :=
      ⟨by rw [hstack, hws]; exact Matches.entry d.params vs ws below hlen hargs, halign⟩
    refine (compile_expr_spec defs n hcalls d.body _ _ _ st hsc).ret.mono ?_
    rintro v s' ⟨s, ⟨henc, hs, hg, hal⟩, rfl⟩
    exact ⟨henc, by simp [hs, hstack], hg, hal⟩

-- by induction on fuel: a call with fuel `n` only makes calls with less fuel
theorem calls_ok : ∀ n, CallsOk defs n :=
  fun n => Nat.strongRecOn n fun n ih => calls_ok_of_spec defs n ih

end

-- for every program and every amount of fuel, the compiled code gives exactly what the
-- interpreter gives: the same value, an error, or running out of fuel. a program that runs
-- forever runs out of fuel for every amount, in both
theorem correctness (prog : Program) (fuel : Nat) :
  Processor.evalToValue fuel (compile prog) = interpret fuel prog :=
  by
    have h := compile_expr_spec prog.defs fuel (fun m _ => calls_ok prog.defs m) prog.main [] [] 0
      initState ⟨.nil, rfl⟩
    simp only [Processor.evalToValue, Processor.evalToState, interpret]
    generalize interp prog.defs fuel [] prog.main = r at h ⊢
    cases r with
    | done v =>
      obtain ⟨st', hrun, hpost⟩ := h
      have hrun' := hrun []
      simp only [List.append_nil, Processor.run_nil] at hrun'
      rw [show (compile prog).funs = funs_of prog.defs from rfl,
        show (compile prog).main = compile_expr (sigs_of prog.defs) [] 0 prog.main from rfl, hrun']
      simp only [hpost.1.decode _ (Nat.lt_succ_self _)]
    | error =>
      have hrun' := h []
      simp only [List.append_nil] at hrun'
      rw [show (compile prog).funs = funs_of prog.defs from rfl,
        show (compile prog).main = compile_expr (sigs_of prog.defs) [] 0 prog.main from rfl, hrun']
    | timeout =>
      have hrun' := h []
      simp only [List.append_nil] at hrun'
      rw [show (compile prog).funs = funs_of prog.defs from rfl,
        show (compile prog).main = compile_expr (sigs_of prog.defs) [] 0 prog.main from rfl, hrun']
