import VerifiedCompiler.Asm
import VerifiedCompiler.Ast

open Directive Operand Register Expr

def num_shift := 2
def num_mask := 0b11
def num_tag := 0b00

def bool_shift := 7
def bool_mask := 0b1111111
def bool_tag := 0b0011111

def true_val := (1 <<< bool_shift) ||| bool_tag
def false_val := (0 <<< bool_shift) ||| bool_tag

def compile_expr : Expr → List Directive
| Num n =>
  [Mov (Reg Rax, Imm (n <<< num_shift))]
| Expr.Bool b =>
  match b with
  | true => [Mov (Reg Rax, Imm true_val)]
  | false => [Mov (Reg Rax, Imm false_val)]
| Sub1 e =>
  (compile_expr e) ++ [Sub (Reg Rax, Imm (1 <<< num_shift))]
| Add1 e =>
  (compile_expr e) ++ [Add (Reg Rax, Imm (1 <<< num_shift))]
-- tagged numbers can be added and subtracted directly: 4a + 4b = 4(a + b)
| Expr.Add e₁ e₂ =>
  compile_expr e₁
  ++ [ Push (Reg Rax) ]
  ++ compile_expr e₂
  ++ [ Pop Rcx, Add (Reg Rax, Reg Rcx) ]
| Expr.Sub e₁ e₂ =>
  compile_expr e₁
  ++ [ Push (Reg Rax) ]
  ++ compile_expr e₂
  ++ [ Pop Rcx, Sub (Reg Rcx, Reg Rax), Mov (Reg Rax, Reg Rcx) ]
| IsZero e =>
  compile_expr e
  ++ [ Cmp (Reg Rax, Imm 0),
       Mov (Reg Rax, Imm true_val),
       Je 1,                          -- if it was zero, skip setting rax to false
       Mov (Reg Rax, Imm false_val) ]
| Lt e₁ e₂ =>
  compile_expr e₁
  ++ [ Push (Reg Rax) ]
  ++ compile_expr e₂
  ++ [ Pop Rcx,
       Cmp (Reg Rcx, Reg Rax),
       Mov (Reg Rax, Imm true_val),
       Jb 1,                          -- if e₁ < e₂, skip setting rax to false
       Mov (Reg Rax, Imm false_val) ]
| If c t f =>
  compile_expr c
  ++ [ Cmp (Reg Rax, Imm false_val),
       Je ((compile_expr t).length + 1) ]   -- if c is false, skip to the code for f
  ++ compile_expr t
  ++ [ Jmp (compile_expr f).length ]        -- done with t, skip over the code for f
  ++ compile_expr f
