import VerifiedCompiler.Asm
import VerifiedCompiler.Ast

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

def Processor.eval (ds : List Directive) : Nat := (evalToState ds).rax
