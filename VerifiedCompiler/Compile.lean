import VerifiedCompiler.Asm
import VerifiedCompiler.Ast

open Directive Operand Register Expr

def num_shift := 2
def num_mask := 0b11
def num_tag := 0b00

def bool_shift := 7
def bool_mask := 0b1111111
def bool_tag := 0b0011111

def compile_expr : Expr → List Directive
| Num n =>
  [Mov (Reg Rax, Imm (n <<< num_shift))]
| Expr.Bool b =>
  match b with
  | true => [Mov (Reg Rax, Imm ((1 <<< bool_shift) ||| bool_tag))]
  | false => [Mov (Reg Rax, Imm ((0 <<< bool_shift) ||| bool_tag))]
| Sub1 e =>
  (compile_expr e) ++ [Sub (Reg Rax, Imm (1 <<< num_shift))]
| Add1 e =>
  (compile_expr e) ++ [Add (Reg Rax, Imm (1 <<< num_shift))]
