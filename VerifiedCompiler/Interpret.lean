import VerifiedCompiler.Asm
import VerifiedCompiler.Ast

open Directive Operand Register Expr

inductive Value
| Integer (i : Nat)
| Boolean (b : Bool)

open Value

-- `none` means the program has a type error, e.g. `Add1 (Bool true)`
def interpret_expr : Expr → Option Value
| Num n => some (Integer n)
| Expr.Bool b => some (Boolean b)
| Add1 e =>
  match (interpret_expr e) with
  | some (Integer i) => some (Integer (i + 1))
  | _ => none
| Sub1 e =>
  match (interpret_expr e) with
  | some (Integer i) => some (Integer (i - 1))
  | _ => none
| Expr.Add e₁ e₂ =>
  match interpret_expr e₁, interpret_expr e₂ with
  | some (Integer i₁), some (Integer i₂) => some (Integer (i₁ + i₂))
  | _, _ => none
| Expr.Sub e₁ e₂ =>
  match interpret_expr e₁, interpret_expr e₂ with
  | some (Integer i₁), some (Integer i₂) => some (Integer (i₁ - i₂))
  | _, _ => none
| IsZero e =>
  match (interpret_expr e) with
  | some (Integer i) => some (Boolean (decide (i = 0)))
  | _ => none
| Lt e₁ e₂ =>
  match interpret_expr e₁, interpret_expr e₂ with
  | some (Integer i₁), some (Integer i₂) => some (Boolean (decide (i₁ < i₂)))
  | _, _ => none
| If c t f =>
  -- only the branch that's taken gets evaluated
  match (interpret_expr c) with
  | some (Boolean true) => interpret_expr t
  | some (Boolean false) => interpret_expr f
  | _ => none
