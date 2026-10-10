import VerifiedCompiler.Asm
import VerifiedCompiler.Compile
import VerifiedCompiler.Interpret

open Directive Operand Register Expr Value

structure ProcessorState where
  rax : Nat
  rcx : Nat
  r8 : Nat
  r15 : Nat
  stack : List Nat
  mem : Nat → Nat     -- the heap, by byte address
  -- `Cmp` sets the flags. `Add`, `Sub`, `And` and `Drop` change them too on a real processor,
  -- so here they wipe them, and a conditional jump on a wiped flag is an error
  zf : Option Bool    -- zero flag: the operands of the last `Cmp` were equal
  cf : Option Bool    -- carry flag: the first operand of the last `Cmp` was below the second

def ProcessorState.regVal (st : ProcessorState) : Register → Nat
| Rax => st.rax
| Rcx => st.rcx
| R8 => st.r8
| R15 => st.r15

def ProcessorState.opVal (st : ProcessorState) : Operand → Nat
| Imm i => i
| Reg r => st.regVal r

def ProcessorState.setReg (st : ProcessorState) (val : Nat) : Register → ProcessorState
| Rax => { st with rax := val }
| Rcx => { st with rcx := val }
| R8 => { st with r8 := val }
| R15 => { st with r15 := val }

def ProcessorState.stackPush (st : ProcessorState) (val : Nat) : ProcessorState
  := { st with stack := val :: st.stack }

-- pops the top of the stack into register `r`. compiled code never pops an empty stack
-- (every pop is matched by an earlier push), so that case is just a no-op
def ProcessorState.stackPop (st : ProcessorState) (r : Register) : ProcessorState :=
  match st.stack with
  | [] => st
  | v :: rest => { st.setReg v r with stack := rest }

def ProcessorState.store (st : ProcessorState) (addr val : Nat) : ProcessorState :=
  { st with mem := fun a => if a = addr then val else st.mem a }

-- what one directive does to the state. jumps only decide which directive runs next (see
-- `skip`), and `Call`, `Ret` and `Error` are handled by `Processor.run`
def processDirective (st : ProcessorState) : Directive → ProcessorState
| Mov (Reg r, o) => st.setReg (st.opVal o) r
| Mov (Imm _, _) => st
| Directive.Add (Reg r, o) => { st.setReg (st.regVal r + st.opVal o) r with zf := none, cf := none }
| Directive.Add (Imm _, _) => st
| Directive.Sub (Reg r, o) => { st.setReg (st.regVal r - st.opVal o) r with zf := none, cf := none }
| Directive.Sub (Imm _, _) => st
| Directive.And (Reg r, o) =>
  { st.setReg (st.regVal r &&& st.opVal o) r with zf := none, cf := none }
| Directive.And (Imm _, _) => st
| Push o => st.stackPush (st.opVal o)
| Pop r => st.stackPop r
| Load k => { st with rax := st.stack.getD k 0 }
| LoadMem dst base off => st.setReg (st.mem (st.regVal base + off)) dst
| StoreMem base off src => st.store (st.regVal base + off) (st.regVal src)
| Cmp (a, b) =>
  { st with zf := some (st.opVal a == st.opVal b), cf := some (decide (st.opVal a < st.opVal b)) }
| Drop n => { st with stack := st.stack.drop n, zf := none, cf := none }
| _ => st

-- how many of the following directives to skip over after this one. `none` means a
-- conditional jump on a flag that nothing set
def ProcessorState.skip (st : ProcessorState) : Directive → Option Nat
| Jmp n => some n
| Je n => st.zf.map (fun z => if z then n else 0)
| Jne n => st.zf.map (fun z => if z then 0 else n)
| Jb n => st.cf.map (fun c => if c then n else 0)
| _ => some 0

-- runs `ds`, with the compiled functions in `funs`. `Call` pushes a return address and runs
-- the function until its `Ret`, and uses up one unit of fuel
def Processor.run (funs : List (String × List Directive)) (fuel : Nat) (st : ProcessorState) :
    List Directive → Outcome ProcessorState
| [] => .done st
| Error :: _ => .error
| Ret :: _ => .done { st with stack := st.stack.drop 1 }
| Call f :: rest =>
  match fuel with
  | 0 => .timeout
  | fuel + 1 =>
    match funs.lookup f with
    | none => .error
    | some body =>
      match Processor.run funs fuel (st.stackPush 0) body with
      | .done st' => Processor.run funs (fuel + 1) st' rest
      | .error => .error
      | .timeout => .timeout
| d :: rest =>
  match st.skip d with
  | none => .error
  | some n => Processor.run funs fuel (processDirective st d) (rest.drop n)
termination_by ds => (fuel, ds.length)
decreasing_by
  all_goals first
    | (apply Prod.Lex.left; omega)
    | (apply Prod.Lex.right; simp only [List.length_drop, List.length_cons]; omega)

def initState : ProcessorState :=
  { rax := 0, rcx := 0, r8 := 0, r15 := 0, stack := [], mem := fun _ => 0,
    zf := none, cf := none }

def Processor.evalToState (fuel : Nat) (c : Compiled) : Outcome ProcessorState :=
  Processor.run c.funs fuel initState c.main

-- read a value back out of its tagged encoding, following pairs into the heap. `n` is how
-- deep to go, so that this stops even on garbage
def decode (mem : Nat → Nat) : Nat → Nat → Value
| 0, _ => Integer 0
| n + 1, w =>
  if w &&& num_mask = num_tag then
    Integer (w >>> num_shift)
  else if w &&& bool_mask = bool_tag then
    Boolean (w >>> bool_shift != 0)
  else if w &&& heap_mask = pair_tag then
    Pair (decode mem n (mem (w - pair_tag))) (decode mem n (mem (w - pair_tag + 8)))
  else Integer 0

-- the answer in rax at the end. a pair takes 16 bytes of heap, so values can't be nested
-- deeper than the heap pointer
def Processor.evalToValue (fuel : Nat) (c : Compiled) : Outcome Value :=
  match Processor.evalToState fuel c with
  | .done st => .done (decode st.mem (st.r15 + 1) st.rax)
  | .error => .error
  | .timeout => .timeout
