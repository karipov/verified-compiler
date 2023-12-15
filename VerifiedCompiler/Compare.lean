import VerifiedCompiler.Process
import VerifiedCompiler.Compile
import VerifiedCompiler.Interpret

import VerifiedCompiler.LoVelib
import Mathlib.Data.Int.Bitwise

open Value Expr

def Processor.evalToValue (ds : List Directive) : Value :=
  match Processor.eval ds with
  | Sum.inl n => Integer n
  | Sum.inr b => Boolean b

theorem shl_shr (n sh : Nat) : n <<< sh >>> sh = n :=
  by
    sorry

theorem smth (n sh : Nat) : (n * sh ^ 2) >>> sh = n := sorry

theorem land_helper (n : Nat) : n * 2 ^ 2 &&& 3 = 0 := sorry

-- the compiler will produce the same value when the interpreter produces a some
-- change the correctness theorem to say that the interpreter produces a some

thoerem compile_smth : ∀ b : Bool, compile_expr (Expr.Bool b) =

theorem correctness : ∀ prog : Expr,
  (interpret_expr prog).isSome →
  Processor.evalToValue (compile_expr prog) = interpret_expr prog
  | Expr.Num n =>
    by
      simp [Processor.evalToValue, Processor.eval, Processor.evalToState, processDirective, compile_expr, interpret_expr, List.foldl, ProcessorState.setReg, ProcessorState.opVal]
      simp [num_tag, num_shift, num_mask, land_helper, shl_shr, smth]

  | Expr.Bool b =>
    by
      simp [Processor.evalToValue, Processor.eval, Processor.evalToState, compile_expr]
      simp [bool_tag, bool_shift, bool_mask]


  | Expr.Sub1 e =>
    by
      -- have ih := correctness e
      -- simp [Processor.evalToValue, Processor.eval, Processor.evalToState, interpret_expr] at *
      -- rw [←ih]
      -- simp
      -- rw [compile_expr]
      -- sorry
      -- cases (compile_expr e) with
      -- | nil =>
      --   simp
      --   sorry

      -- | cons hd tl =>
      --   have hfold_concat :=
      --     List.foldl_concat processDirective { rax := 0 }
      --       (Directive.Sub (Operand.Reg Register.Rax, Operand.Imm 1)) (hd :: tl)
      --   -- rw [hfold_concat]
        -- rfl
        sorry

  | Expr.Add1 e =>
    by
      -- have ih := correctness e
      -- simp [Processor.evalToValue, Processor.eval, Processor.evalToState, interpret_expr] at *
      -- rw [←ih]
      -- simp
      -- rw [compile_expr]
      -- sorry
      -- cases (compile_expr e) with
      -- | nil =>
      --   simp
      --   sorry
      -- | cons hd tl =>
      --   have hfold_concat := List.foldl_concat processDirective { rax := 0 }
      --       (Directive.Add (Operand.Reg Register.Rax, Operand.Imm 1)) (hd :: tl)
        -- rw [hfold_concat]
        -- rfl
        sorry
