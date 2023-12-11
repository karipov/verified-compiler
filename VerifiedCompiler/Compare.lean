import VerifiedCompiler.Process
import VerifiedCompiler.Compile
import VerifiedCompiler.Interpret

import VerifiedCompiler.LoVelib

open Value Expr

def Processor.evalToValue (ds : List Directive) : Value :=
  Integer (Processor.eval ds)


-- lemma smaller_step

lemma step
  (prog : Expr)
  (n : Nat)
  (hypo : Processor.evalToValue (compile_expr (prog)) = Integer n) :
  Processor.evalToValue (compile_expr (Sub1 prog)) = Integer (n - 1)
  :=
    by
      simp [Processor.evalToValue, Processor.eval, Processor.evalToState,
            ProcessorState.setReg, ProcessorState.opVal] at *
      sorry

theorem correctness :
  ∀ prog : Expr, Processor.evalToValue (compile_expr prog) = interpret_expr prog
  | Expr.Num n =>
    by
      simp [Processor.evalToValue, Processor.eval, Processor.evalToState,
      processDirective, ProcessorState.setReg, ProcessorState.opVal, interpret_expr]

  | Expr.Sub1 e =>
    by
      have ih := correctness e
      simp [Processor.evalToValue, Processor.eval, Processor.evalToState, compile_expr] at *
      -- simp [interpret_expr] at *





      -- have modified_ih :
      --   Integer (processDirective (List.foldl processDirective { rax := 0 } (compile_expr e)) (Directive.Sub (Operand.Reg Register.Rax, Operand.Imm 1))).rax
      --   = Integer ((List.foldl processDirective { rax := 0 } (compile_expr e)).rax - 1)
      --     :=






  | Expr.Add1 e => by sorry
