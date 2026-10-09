import VerifiedCompiler.Asm
import VerifiedCompiler.Ast

open Directive Operand Register Expr

structure ProcessorState where
  rax : Nat
  rcx : Nat
  stack : List Nat

def ProcessorState.regVal (st : ProcessorState) : Register → Nat
| Rax => st.rax
| Rcx => st.rcx

def ProcessorState.opVal (st : ProcessorState) : Operand → Nat
| Imm i => i
| Reg r => st.regVal r

def ProcessorState.setReg (st : ProcessorState) (val : Nat) : Register → ProcessorState
| Rax => { st with rax := val }
| Rcx => { st with rcx := val }

def ProcessorState.stackPush (st : ProcessorState) (val : Nat) : ProcessorState
  := { st with stack := val :: st.stack }

-- pops the top of the stack into register `r`. compiled code never pops an empty stack
-- (every pop is matched by an earlier push), so that case is just a no-op
def ProcessorState.stackPop (st : ProcessorState) (r : Register) : ProcessorState :=
  match st.stack with
  | [] => st
  | v :: rest => { st.setReg v r with stack := rest }

def processDirective (st : ProcessorState) : Directive → ProcessorState
| Mov (Reg r, o) => st.setReg (st.opVal o) r
| Mov (Imm _, _) => st
| Push o => st.stackPush (st.opVal o)
| Pop r => st.stackPop r
| Directive.Add (Reg r, o) => st.setReg (st.regVal r + st.opVal o) r
| Directive.Add (Imm _, _) => st
| Directive.Sub (Reg r, o) => st.setReg (st.regVal r - st.opVal o) r
| Directive.Sub (Imm _, _) => st

@[simp] def Processor.evalToState : List Directive → ProcessorState :=
List.foldl processDirective {rax := 0, rcx := 0, stack := []}

@[simp] def Processor.eval (ds : List Directive) : Nat := (evalToState ds).rax
