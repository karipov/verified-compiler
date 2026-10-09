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

-- the stack slot holding every variable in scope (slots count up from the bottom of the stack)
abbrev Symtab := List (String × Nat)

-- sets the zero flag if the value in rax has the given tag. r8 is a scratch register so that
-- rax keeps the value
def tag_test (mask tag : Nat) : List Directive :=
  [ Mov (Reg R8, Reg Rax),
    Directive.And (Reg R8, Imm mask),
    Cmp (Reg R8, Imm tag) ]

-- calls the error handler unless the value in rax has the given tag
def ensure (mask tag : Nat) : List Directive :=
  tag_test mask tag ++ [ Je 1, Error ]  -- if the tag matched, skip over the error

def ensure_num := ensure num_mask num_tag
def ensure_bool := ensure bool_mask bool_tag

-- turn a flag into a boolean in rax
def zf_to_bool : List Directive :=
  [ Mov (Reg Rax, Imm true_val),
    Je 1,                           -- if the flag is set, skip setting rax to false
    Mov (Reg Rax, Imm false_val) ]

def cf_to_bool : List Directive :=
  [ Mov (Reg Rax, Imm true_val),
    Jb 1,
    Mov (Reg Rax, Imm false_val) ]

-- `depth` is how many slots are already on the stack, so it's also the next free slot
def compile_expr (tab : Symtab) (depth : Nat) : Expr → List Directive
| Num n =>
  [Mov (Reg Rax, Imm (n <<< num_shift))]
| Expr.Bool b =>
  match b with
  | true => [Mov (Reg Rax, Imm true_val)]
  | false => [Mov (Reg Rax, Imm false_val)]
| Sub1 e =>
  compile_expr tab depth e ++ ensure_num ++ [Sub (Reg Rax, Imm (1 <<< num_shift))]
| Add1 e =>
  compile_expr tab depth e ++ ensure_num ++ [Add (Reg Rax, Imm (1 <<< num_shift))]
-- tagged numbers can be added and subtracted directly: 4a + 4b = 4(a + b)
| Expr.Add e₁ e₂ =>
  compile_expr tab depth e₁ ++ ensure_num
  ++ [ Push (Reg Rax) ]
  ++ compile_expr tab (depth + 1) e₂ ++ ensure_num
  ++ [ Pop Rcx, Add (Reg Rax, Reg Rcx) ]
| Expr.Sub e₁ e₂ =>
  compile_expr tab depth e₁ ++ ensure_num
  ++ [ Push (Reg Rax) ]
  ++ compile_expr tab (depth + 1) e₂ ++ ensure_num
  ++ [ Pop Rcx, Sub (Reg Rcx, Reg Rax), Mov (Reg Rax, Reg Rcx) ]
| IsZero e =>
  compile_expr tab depth e ++ ensure_num
  ++ [ Cmp (Reg Rax, Imm 0) ]
  ++ zf_to_bool
| Lt e₁ e₂ =>
  compile_expr tab depth e₁ ++ ensure_num
  ++ [ Push (Reg Rax) ]
  ++ compile_expr tab (depth + 1) e₂ ++ ensure_num
  ++ [ Pop Rcx, Cmp (Reg Rcx, Reg Rax) ]
  ++ cf_to_bool
| If c t f =>
  compile_expr tab depth c ++ ensure_bool
  ++ [ Cmp (Reg Rax, Imm false_val),
       Je ((compile_expr tab depth t).length + 1) ]   -- if c is false, skip to the code for f
  ++ compile_expr tab depth t
  ++ [ Jmp (compile_expr tab depth f).length ]        -- done with t, skip over the code for f
  ++ compile_expr tab depth f
| Expr.Not e =>
  compile_expr tab depth e ++ ensure_bool
  ++ [ Cmp (Reg Rax, Imm false_val) ]
  ++ zf_to_bool
-- every value has exactly one encoding, so comparing encodings compares values
| Expr.Eq e₁ e₂ =>
  compile_expr tab depth e₁
  ++ [ Push (Reg Rax) ]
  ++ compile_expr tab (depth + 1) e₂
  ++ [ Pop Rcx, Cmp (Reg Rcx, Reg Rax) ]
  ++ zf_to_bool
| Expr.And e₁ e₂ =>
  compile_expr tab depth e₁ ++ ensure_bool
  ++ [ Cmp (Reg Rax, Imm false_val),
       Je (compile_expr tab depth e₂ ++ ensure_bool).length ]  -- false already: skip e₂
  ++ compile_expr tab depth e₂ ++ ensure_bool
| Expr.Or e₁ e₂ =>
  compile_expr tab depth e₁ ++ ensure_bool
  ++ [ Cmp (Reg Rax, Imm true_val),
       Je (compile_expr tab depth e₂ ++ ensure_bool).length ]  -- true already: skip e₂
  ++ compile_expr tab depth e₂ ++ ensure_bool
| IsNum e =>
  compile_expr tab depth e ++ tag_test num_mask num_tag ++ zf_to_bool
| IsBool e =>
  compile_expr tab depth e ++ tag_test bool_mask bool_tag ++ zf_to_bool
| Var x =>
  match tab.lookup x with
  | some slot => [ Load slot ]
  | none => [ Error ]  -- the variable isn't in scope
| Let x e body =>
  compile_expr tab depth e
  ++ [ Push (Reg Rax) ]                                   -- e's value goes in slot `depth`
  ++ compile_expr ((x, depth) :: tab) (depth + 1) body
  ++ [ Pop Rcx ]                                          -- and the slot is freed again

def compile (prog : Expr) : List Directive :=
  compile_expr [] 0 prog
