import VerifiedCompiler.Asm
import VerifiedCompiler.Compile

open Directive Operand Register Expr

structure ProcessorState where
  rax : Nat
  rcx : Nat
  r8 : Nat
  stack : List Nat
  zf : Bool  -- zero flag: set by `Cmp` when both operands are equal
  cf : Bool  -- carry flag: set by `Cmp` when the first operand is below the second

def ProcessorState.regVal (st : ProcessorState) : Register → Nat
| Rax => st.rax
| Rcx => st.rcx
| R8 => st.r8

def ProcessorState.opVal (st : ProcessorState) : Operand → Nat
| Imm i => i
| Reg r => st.regVal r

def ProcessorState.setReg (st : ProcessorState) (val : Nat) : Register → ProcessorState
| Rax => { st with rax := val }
| Rcx => { st with rcx := val }
| R8 => { st with r8 := val }

def ProcessorState.stackPush (st : ProcessorState) (val : Nat) : ProcessorState
  := { st with stack := val :: st.stack }

-- pops the top of the stack into register `r`. compiled code never pops an empty stack
-- (every pop is matched by an earlier push), so that case is just a no-op
def ProcessorState.stackPop (st : ProcessorState) (r : Register) : ProcessorState :=
  match st.stack with
  | [] => st
  | v :: rest => { st.setReg v r with stack := rest }

-- slot `i` of the stack, counting up from the bottom, so pushing more values doesn't move
-- it. compiled code only loads slots that are on the stack, so the default never comes up
def ProcessorState.slot (st : ProcessorState) (i : Nat) : Nat :=
  st.stack.reverse.getD i 0

-- jumps don't change the state, they only decide which directive runs next (see `skip`).
-- `Error` doesn't get here either: `Processor.run` stops when it reaches one
def processDirective (st : ProcessorState) : Directive → ProcessorState
| Mov (Reg r, o) => st.setReg (st.opVal o) r
| Mov (Imm _, _) => st
| Push o => st.stackPush (st.opVal o)
| Pop r => st.stackPop r
| Load i => { st with rax := st.slot i }
| Directive.Add (Reg r, o) => st.setReg (st.regVal r + st.opVal o) r
| Directive.Add (Imm _, _) => st
| Directive.Sub (Reg r, o) => st.setReg (st.regVal r - st.opVal o) r
| Directive.Sub (Imm _, _) => st
| Directive.And (Reg r, o) => st.setReg (st.regVal r &&& st.opVal o) r
| Directive.And (Imm _, _) => st
| Cmp (a, b) => { st with zf := st.opVal a == st.opVal b, cf := decide (st.opVal a < st.opVal b) }
| Jmp _ => st
| Je _ => st
| Jb _ => st
| Error => st

-- how many of the following directives to skip over after this one
def ProcessorState.skip (st : ProcessorState) : Directive → Nat
| Jmp n => n
| Je n => if st.zf then n else 0
| Jb n => if st.cf then n else 0
| _ => 0

-- `none` means the program ended in an error
def Processor.run (st : ProcessorState) : List Directive → Option ProcessorState
| [] => some st
| Error :: _ => none
| d :: rest => Processor.run (processDirective st d) (rest.drop (st.skip d))
termination_by ds => ds.length
decreasing_by simp; omega

def Processor.evalToState : List Directive → Option ProcessorState :=
Processor.run {rax := 0, rcx := 0, r8 := 0, stack := [], zf := false, cf := false}

-- read a value back out of its tagged encoding
def Processor.decode (retval : Nat) : Nat ⊕ Bool :=
if retval &&& num_mask = num_tag then
  Sum.inl (retval >>> num_shift)
else if retval &&& bool_mask = bool_tag then
  if retval >>> bool_shift = 0 then Sum.inr false else Sum.inr true
else Sum.inl 0

def Processor.eval (ds : List Directive) : Option (Nat ⊕ Bool) :=
match Processor.evalToState ds with
| some st => some (Processor.decode st.rax)
| none => none
