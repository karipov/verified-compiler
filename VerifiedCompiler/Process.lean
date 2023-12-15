import VerifiedCompiler.Asm
import VerifiedCompiler.Compile

open Directive Operand Register Expr

structure ProcessorState where
  rax : Nat

def ProcessorState.regVal (st : ProcessorState) : Register → Nat
| Rax => st.rax

def ProcessorState.opVal (st : ProcessorState) : Operand → Nat
| Imm i => i
| Reg r => st.regVal r

def ProcessorState.setReg (st : ProcessorState) (val : Nat) : Register → ProcessorState
| Rax => { st with rax := val }

def processDirective (st : ProcessorState) : Directive → ProcessorState
| Mov (Reg r, o) => st.setReg (st.opVal o) r
| Mov (Imm _, _) => st
| Directive.Add (Reg r, o) => st.setReg (st.regVal r + st.opVal o) r
| Directive.Add (Imm _, _) => st
| Directive.Sub (Reg r, o) => st.setReg (st.regVal r - st.opVal o) r
| Directive.Sub (Imm _, _) => st

def Processor.evalToState : List Directive → ProcessorState :=
List.foldl processDirective {rax := 0}

def Processor.eval (ds : List Directive) : Nat ⊕ Bool :=
let retval := (evalToState ds).rax;
if retval &&& num_mask = num_tag then
  Sum.inl (retval >>> num_shift)
else if retval &&& bool_mask = bool_tag then
  if retval >>> bool_shift = 0 then Sum.inr false else Sum.inr true
else Sum.inl 0
