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

-- a pair is a pointer to two words on the heap. pointers are multiples of 8, so the low three
-- bits are free for the tag
def heap_mask := 0b111
def pair_tag := 0b010

-- where each variable in scope lives: its slot in the current stack frame. slots count up
-- from the bottom of the frame, so pushing more values doesn't move them
abbrev Symtab := List (String × Nat)

-- how many parameters each function takes
abbrev Sigs := List (String × Nat)

-- sets the zero flag if the value in rax has the given tag. r8 is a scratch register so that
-- rax keeps the value
def tag_test (mask tag : Nat) : List Directive :=
  [ Mov (Reg R8, Reg Rax),
    Directive.And (Reg R8, Imm mask),
    Cmp (Reg R8, Imm tag) ]

-- calls the error handler unless the value in rax has the given tag
def ensure (mask tag : Nat) : List Directive :=
  tag_test mask tag ++ [ Je 1, Error ]  -- if the tag matched, skip over the error

-- calls the error handler if the value in rax has the given tag
def ensure_not (mask tag : Nat) : List Directive :=
  tag_test mask tag ++ [ Jne 1, Error ]

def ensure_num := ensure num_mask num_tag
def ensure_bool := ensure bool_mask bool_tag
def ensure_pair := ensure heap_mask pair_tag
def ensure_atom := ensure_not heap_mask pair_tag

-- turn a flag into a boolean in rax
def zf_to_bool : List Directive :=
  [ Mov (Reg Rax, Imm true_val),
    Je 1,                           -- if the flag is set, skip setting rax to false
    Mov (Reg Rax, Imm false_val) ]

def cf_to_bool : List Directive :=
  [ Mov (Reg Rax, Imm true_val),
    Jb 1,
    Mov (Reg Rax, Imm false_val) ]

mutual
-- `depth` is how many values are in the current stack frame, so it's also the next free slot.
-- slot `i` is `depth - 1 - i` values down from the top of the stack
def compile_expr (sigs : Sigs) (tab : Symtab) (depth : Nat) : Expr → List Directive
| Num n =>
  [Mov (Reg Rax, Imm (n <<< num_shift))]
| Expr.Bool b =>
  match b with
  | true => [Mov (Reg Rax, Imm true_val)]
  | false => [Mov (Reg Rax, Imm false_val)]
| Sub1 e =>
  compile_expr sigs tab depth e ++ ensure_num ++ [Sub (Reg Rax, Imm (1 <<< num_shift))]
| Add1 e =>
  compile_expr sigs tab depth e ++ ensure_num ++ [Add (Reg Rax, Imm (1 <<< num_shift))]
-- tagged numbers can be added and subtracted directly: 4a + 4b = 4(a + b)
| Expr.Add e₁ e₂ =>
  compile_expr sigs tab depth e₁ ++ ensure_num
  ++ [ Push (Reg Rax) ]
  ++ compile_expr sigs tab (depth + 1) e₂ ++ ensure_num
  ++ [ Pop Rcx, Add (Reg Rax, Reg Rcx) ]
| Expr.Sub e₁ e₂ =>
  compile_expr sigs tab depth e₁ ++ ensure_num
  ++ [ Push (Reg Rax) ]
  ++ compile_expr sigs tab (depth + 1) e₂ ++ ensure_num
  ++ [ Pop Rcx, Sub (Reg Rcx, Reg Rax), Mov (Reg Rax, Reg Rcx) ]
| IsZero e =>
  compile_expr sigs tab depth e ++ ensure_num
  ++ [ Cmp (Reg Rax, Imm 0) ]
  ++ zf_to_bool
| Lt e₁ e₂ =>
  compile_expr sigs tab depth e₁ ++ ensure_num
  ++ [ Push (Reg Rax) ]
  ++ compile_expr sigs tab (depth + 1) e₂ ++ ensure_num
  ++ [ Pop Rcx, Cmp (Reg Rcx, Reg Rax) ]
  ++ cf_to_bool
| If c t f =>
  compile_expr sigs tab depth c ++ ensure_bool
  ++ [ Cmp (Reg Rax, Imm false_val),
       Je ((compile_expr sigs tab depth t).length + 1) ]  -- if c is false, skip to f
  ++ compile_expr sigs tab depth t
  ++ [ Jmp (compile_expr sigs tab depth f).length ]       -- done with t, skip over f
  ++ compile_expr sigs tab depth f
| Expr.Not e =>
  compile_expr sigs tab depth e ++ ensure_bool
  ++ [ Cmp (Reg Rax, Imm false_val) ]
  ++ zf_to_bool
-- numbers and booleans have exactly one encoding each, so comparing encodings compares values
| Expr.Eq e₁ e₂ =>
  compile_expr sigs tab depth e₁ ++ ensure_atom
  ++ [ Push (Reg Rax) ]
  ++ compile_expr sigs tab (depth + 1) e₂ ++ ensure_atom
  ++ [ Pop Rcx, Cmp (Reg Rcx, Reg Rax) ]
  ++ zf_to_bool
| Expr.And e₁ e₂ =>
  compile_expr sigs tab depth e₁ ++ ensure_bool
  ++ [ Cmp (Reg Rax, Imm false_val),
       Je (compile_expr sigs tab depth e₂ ++ ensure_bool).length ]  -- false already: skip e₂
  ++ compile_expr sigs tab depth e₂ ++ ensure_bool
| Expr.Or e₁ e₂ =>
  compile_expr sigs tab depth e₁ ++ ensure_bool
  ++ [ Cmp (Reg Rax, Imm true_val),
       Je (compile_expr sigs tab depth e₂ ++ ensure_bool).length ]  -- true already: skip e₂
  ++ compile_expr sigs tab depth e₂ ++ ensure_bool
| IsNum e =>
  compile_expr sigs tab depth e ++ tag_test num_mask num_tag ++ zf_to_bool
| IsBool e =>
  compile_expr sigs tab depth e ++ tag_test bool_mask bool_tag ++ zf_to_bool
| Var x =>
  match tab.lookup x with
  | some slot => [ Load (depth - 1 - slot) ]
  | none => [ Error ]  -- the variable isn't in scope
| Let x e body =>
  compile_expr sigs tab depth e
  ++ [ Push (Reg Rax) ]                                        -- e's value goes in slot `depth`
  ++ compile_expr sigs ((x, depth) :: tab) (depth + 1) body
  ++ [ Pop Rcx ]                                               -- and the slot is freed again
-- the pair goes at the heap pointer: e₁'s value, then e₂'s value, and the heap pointer moves
-- past them
| Expr.Pair e₁ e₂ =>
  compile_expr sigs tab depth e₁
  ++ [ Push (Reg Rax) ]
  ++ compile_expr sigs tab (depth + 1) e₂
  ++ [ Pop Rcx,
       StoreMem R15 0 Rcx,
       StoreMem R15 8 Rax,
       Mov (Reg Rax, Reg R15),
       Add (Reg Rax, Imm pair_tag),
       Add (Reg R15, Imm 16) ]
| Left e =>
  compile_expr sigs tab depth e ++ ensure_pair
  ++ [ Sub (Reg Rax, Imm pair_tag), LoadMem Rax Rax 0 ]
| Right e =>
  compile_expr sigs tab depth e ++ ensure_pair
  ++ [ Sub (Reg Rax, Imm pair_tag), LoadMem Rax Rax 8 ]
| IsPair e =>
  compile_expr sigs tab depth e ++ tag_test heap_mask pair_tag ++ zf_to_bool
-- push the arguments, call, then throw the arguments away again
| App f args =>
  match sigs.lookup f with
  | some n =>
    if args.length = n then compile_args sigs tab depth args ++ [ Call f, Drop n ]
    else [ Error ]  -- wrong number of arguments
  | none => [ Error ]  -- no such function

def compile_args (sigs : Sigs) (tab : Symtab) (depth : Nat) : List Expr → List Directive
| [] => []
| e :: es => compile_expr sigs tab depth e ++ [ Push (Reg Rax) ] ++ compile_args sigs tab (depth + 1) es
end

-- when a function starts, its frame holds the arguments (the last one on top) and then the
-- return address. so parameter `i` is in slot `i`, and the body starts at depth `n + 1`
def param_tab (params : List String) : Symtab :=
  params.zipIdx

def compile_defn (sigs : Sigs) (d : Defn) : List Directive :=
  compile_expr sigs (param_tab d.params) (d.params.length + 1) d.body ++ [ Ret ]

structure Compiled where
  main : List Directive
  funs : List (String × List Directive)

def sigs_of (defs : List Defn) : Sigs :=
  defs.map (fun d => (d.name, d.params.length))

def compile (prog : Program) : Compiled :=
  { main := compile_expr (sigs_of prog.defs) [] 0 prog.main,
    funs := prog.defs.map (fun d => (d.name, compile_defn (sigs_of prog.defs) d)) }
