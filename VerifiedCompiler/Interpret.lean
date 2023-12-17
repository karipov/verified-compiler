import VerifiedCompiler.Asm
import VerifiedCompiler.Ast

open Directive Operand Register Expr

inductive Value
| Integer (i : Nat)

open Value

def interpret_expr : Expr → Value
| Num n => Integer n
| Add1 e =>
  match (interpret_expr e) with
  | Integer i => Integer (i + 1)
| Sub1 e =>
  match (interpret_expr e) with
  | Integer i => Integer (i - 1)
| Expr.Add e1 e2 =>
  match (interpret_expr e1, interpret_expr e2) with
  | (Integer i1, Integer i2) => Integer (i1 + i2)
