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
