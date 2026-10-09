import VerifiedCompiler.Process
import VerifiedCompiler.Compile
import VerifiedCompiler.Interpret

open Value Expr Directive Register Operand

@[simp] def Processor.evalToValue (ds : List Directive) : Value :=
  Integer (Processor.eval ds)


theorem moving
    (prog : Expr) (st_nopush st_push : ProcessorState)
    (eval_nopush : Processor.evalToState (compile_expr prog) = st_nopush)
    (eval_push : Processor.evalToState (compile_expr prog ++ [Push (Reg Rax)]) = st_push)
    : st_push = { st_nopush with stack := st_push.rax :: st_nopush.stack }
    :=
    by
      subst eval_nopush eval_push
      simp [List.foldl_append, processDirective, ProcessorState.stackPush,
        ProcessorState.opVal, ProcessorState.regVal]


-- `correctness` only talks about running code from the empty starting state, but in
-- `Add e₁ e₂` the code for `e₂` runs with `e₁`'s value already pushed on the stack. so the
-- induction needs a stronger statement that works from *any* starting state: the code for
-- `prog` leaves its value in rax, and leaves the stack exactly the way it found it.
theorem compile_expr_spec :
  ∀ (prog : Expr) (st : ProcessorState),
    Integer (List.foldl processDirective st (compile_expr prog)).rax = interpret_expr prog ∧
    (List.foldl processDirective st (compile_expr prog)).stack = st.stack
  | Expr.Num n, st =>
    by
      simp [compile_expr, interpret_expr, processDirective, ProcessorState.setReg,
        ProcessorState.opVal]

  | Expr.Sub1 e, st =>
    by
      have ⟨ih_rax, ih_stack⟩ := compile_expr_spec e st
      simp only [compile_expr, interpret_expr, List.foldl_append, ← ih_rax]
      simp [processDirective, ProcessorState.setReg, ProcessorState.regVal,
        ProcessorState.opVal, ih_stack]

  | Expr.Add1 e, st =>
    by
      have ⟨ih_rax, ih_stack⟩ := compile_expr_spec e st
      simp only [compile_expr, interpret_expr, List.foldl_append, ← ih_rax]
      simp [processDirective, ProcessorState.setReg, ProcessorState.regVal,
        ProcessorState.opVal, ih_stack]

  | Expr.Add e₁ e₂, st =>
    by
      simp only [compile_expr, interpret_expr, List.foldl_append, List.foldl_cons,
        List.foldl_nil]
      -- st₁: the state after running the code for e₁ from st
      have ⟨ih₁_rax, ih₁_stack⟩ := compile_expr_spec e₁ st
      generalize List.foldl processDirective st (compile_expr e₁) = st₁ at *
      -- st₂: the state after pushing e₁'s value and running the code for e₂ from there
      have ⟨ih₂_rax, ih₂_stack⟩ := compile_expr_spec e₂ (processDirective st₁ (Push (Reg Rax)))
      generalize List.foldl processDirective (processDirective st₁ (Push (Reg Rax)))
        (compile_expr e₂) = st₂ at *
      -- so e₁'s value is sitting on top of the original stack...
      simp only [processDirective, ProcessorState.stackPush, ProcessorState.opVal,
        ProcessorState.regVal, ih₁_stack] at ih₂_stack
      -- ...and popping it into rcx and adding it to e₂'s value gives the right answer
      rw [← ih₁_rax, ← ih₂_rax]
      simp [processDirective, ProcessorState.stackPop, ih₂_stack, ProcessorState.setReg,
        ProcessorState.regVal, ProcessorState.opVal, Nat.add_comm]


theorem correctness :
  ∀ prog : Expr, Processor.evalToValue (compile_expr prog) = interpret_expr prog :=
  fun prog => (compile_expr_spec prog { rax := 0, rcx := 0, stack := [] }).1
