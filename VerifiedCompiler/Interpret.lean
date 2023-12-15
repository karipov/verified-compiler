import VerifiedCompiler.Asm
import VerifiedCompiler.Ast

open Directive Operand Register Expr

inductive Value
| Integer (i : Nat)
| Boolean (b : Bool)

open Value

def interpret_expr : Expr → Option Value
| Num n => some (Integer n)
| Expr.Bool b => some (Boolean b)
| Add1 e =>
  match (interpret_expr e) with
  | Integer i => some (Integer (i + 1))
  | _ => none
| Sub1 e =>
  match (interpret_expr e) with
  | Integer i => some (Integer (i - 1))
  | _ => none
