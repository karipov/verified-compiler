import VerifiedCompiler.Asm
import VerifiedCompiler.Ast

open Directive Operand Register Expr

inductive Value
| Integer (i : Nat)
| Boolean (b : Bool)
deriving DecidableEq, Repr

open Value

def Value.isNum : Value → Bool
| Integer _ => true
| Boolean _ => false

def Value.isBool : Value → Bool
| Integer _ => false
| Boolean _ => true

-- the value of every variable in scope. `Let` puts its variable at the front, so it shadows
-- any outer variable with the same name
abbrev Env := List (String × Value)

-- `none` means the program has an error: a type error like `Add1 (Bool true)`, or a
-- variable that isn't in scope
def interpret_expr (env : Env) : Expr → Option Value
| Num n => some (Integer n)
| Expr.Bool b => some (Boolean b)
| Add1 e =>
  match (interpret_expr env e) with
  | some (Integer i) => some (Integer (i + 1))
  | _ => none
| Sub1 e =>
  match (interpret_expr env e) with
  | some (Integer i) => some (Integer (i - 1))
  | _ => none
| Expr.Add e₁ e₂ =>
  match interpret_expr env e₁, interpret_expr env e₂ with
  | some (Integer i₁), some (Integer i₂) => some (Integer (i₁ + i₂))
  | _, _ => none
| Expr.Sub e₁ e₂ =>
  match interpret_expr env e₁, interpret_expr env e₂ with
  | some (Integer i₁), some (Integer i₂) => some (Integer (i₁ - i₂))
  | _, _ => none
| IsZero e =>
  match (interpret_expr env e) with
  | some (Integer i) => some (Boolean (decide (i = 0)))
  | _ => none
| Lt e₁ e₂ =>
  match interpret_expr env e₁, interpret_expr env e₂ with
  | some (Integer i₁), some (Integer i₂) => some (Boolean (decide (i₁ < i₂)))
  | _, _ => none
| If c t f =>
  -- only the branch that's taken gets evaluated
  match (interpret_expr env c) with
  | some (Boolean true) => interpret_expr env t
  | some (Boolean false) => interpret_expr env f
  | _ => none
| Expr.Not e =>
  match (interpret_expr env e) with
  | some (Boolean b) => some (Boolean (!b))
  | _ => none
-- any two values can be compared, `Eq (Num 1) (Bool true)` is just false
| Expr.Eq e₁ e₂ =>
  match interpret_expr env e₁, interpret_expr env e₂ with
  | some v₁, some v₂ => some (Boolean (decide (v₁ = v₂)))
  | _, _ => none
-- `And` and `Or` short-circuit: e₂ is only evaluated if e₁ doesn't already decide the answer
| Expr.And e₁ e₂ =>
  match (interpret_expr env e₁) with
  | some (Boolean false) => some (Boolean false)
  | some (Boolean true) =>
    match (interpret_expr env e₂) with
    | some (Boolean b) => some (Boolean b)
    | _ => none
  | _ => none
| Expr.Or e₁ e₂ =>
  match (interpret_expr env e₁) with
  | some (Boolean true) => some (Boolean true)
  | some (Boolean false) =>
    match (interpret_expr env e₂) with
    | some (Boolean b) => some (Boolean b)
    | _ => none
  | _ => none
| IsNum e =>
  match (interpret_expr env e) with
  | some v => some (Boolean v.isNum)
  | none => none
| IsBool e =>
  match (interpret_expr env e) with
  | some v => some (Boolean v.isBool)
  | none => none
| Var x => env.lookup x
| Let x e body =>
  match (interpret_expr env e) with
  | some v => interpret_expr ((x, v) :: env) body
  | none => none

def interpret (prog : Expr) : Option Value :=
  interpret_expr [] prog
