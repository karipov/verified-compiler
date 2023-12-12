import VerifiedCompiler.Process
import VerifiedCompiler.Compile
import VerifiedCompiler.Interpret

import VerifiedCompiler.LoVelib

open Value Expr

def Processor.evalToValue (ds : List Directive) : Value :=
  Integer (Processor.eval ds)


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
          List.foldl_concat processDirective { rax := 0 }
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
        have hfold_concat := List.foldl_concat processDirective { rax := 0 }
            (Directive.Add (Operand.Reg Register.Rax, Operand.Imm 1)) (hd :: tl)
        rw [hfold_concat]
        rfl
