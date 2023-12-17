import VerifiedCompiler.Process
import VerifiedCompiler.Compile
import VerifiedCompiler.Interpret

import VerifiedCompiler.LoVelib

open Value Expr Directive Register Operand

@[simp] def Processor.evalToValue (ds : List Directive) : Value :=
  Integer (Processor.eval ds)


theorem moving
    (prog : Expr) (st_nopush st_push : ProcessorState)
    (eval_nopush : Processor.evalToState (compile_expr prog) = st_nopush)
    (eval_push : Processor.evalToState (compile_expr prog ++ [Push (Reg Rax)]) = st_push)
    : st_push = { st_nopush with stack := st_push.rax :: st_nopush.stack }
    :=
    by sorry


#check List.foldl_append

theorem correctness :
  ∀ prog : Expr, Processor.evalToValue (compile_expr prog) = interpret_expr prog
  | Expr.Num n =>
    by
      simp [Processor.evalToValue, Processor.eval, Processor.evalToState,
      processDirective, ProcessorState.setReg, ProcessorState.opVal, interpret_expr]

  | Expr.Sub1 e =>
    by
      have ih := correctness e
      simp [Processor.evalToValue, Processor.eval, Processor.evalToState, interpret_expr] at *
      rw [←ih]
      simp
      rw [compile_expr]
      cases (compile_expr e) with
      | nil => simp
      | cons hd tl =>
        have hfold_concat :=
          List.foldl_concat processDirective { rax := 0, rcx := 0, stack := [] }
            (Directive.Sub (Operand.Reg Register.Rax, Operand.Imm 1)) (hd :: tl)
        rw [hfold_concat]
        rfl

  | Expr.Add1 e =>
    by
      have ih := correctness e
      simp [Processor.evalToValue, Processor.eval, Processor.evalToState, interpret_expr] at *
      rw [←ih]
      simp
      rw [compile_expr]
      cases (compile_expr e) with
      | nil => simp
      | cons hd tl =>
        have hfold_concat := List.foldl_concat processDirective { rax := 0, rcx := 0, stack := [] }
            (Directive.Add (Operand.Reg Register.Rax, Operand.Imm 1)) (hd :: tl)
        rw [hfold_concat]
        rfl
  | Expr.Add e₁ e₂ =>
    by
      have ih₁ := correctness e₁
      have ih₂ := correctness e₂
      simp [interpret_expr] at *
      rw [←ih₁, ←ih₂]
      simp
      rw [compile_expr]

      have smth := moving e₁ (Processor.evalToState (compile_expr e₁))
                            (Processor.evalToState (compile_expr e₁ ++ [Push (Reg Rax)]))
                            (by rfl) (by rfl)
      simp only [Processor.evalToState] at smth
      have llsee := List.foldl_append processDirective { rax := 0, rcx := 0, stack := [] } (compile_expr e₁ ++ [Push (Reg Rax)]) (compile_expr e₂ ++ [Add (Reg Rax, Pop)])
      have heq : (compile_expr e₁ ++ [Push (Reg Rax)]) ++ (compile_expr e₂ ++ [Add (Reg Rax, Pop)])
                = compile_expr e₁ ++ [Push (Reg Rax)] ++ compile_expr e₂ ++ [Add (Reg Rax, Pop)] := by simp
      rw [heq] at llsee
      rw [llsee]
      rw [smth]

      sorry
