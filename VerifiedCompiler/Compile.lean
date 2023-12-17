import VerifiedCompiler.Asm
import VerifiedCompiler.Ast

open Directive Operand Register Expr

def compile_expr : Expr → List Directive
| Num n =>
  [Mov (Reg Rax, Imm n)]
| Sub1 e =>
  (compile_expr e) ++ [Sub (Reg Rax, Imm 1)]
| Add1 e =>
  (compile_expr e) ++ [Add (Reg Rax, Imm 1)]
| Expr.Add e₁ e₂ =>
  compile_expr e₁
  ++ [ Push (Reg Rax) ]
  ++ compile_expr e₂
  ++ [ Add (Reg Rax, Pop) ]
