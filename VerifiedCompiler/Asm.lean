inductive Register
| Rax
| Rcx

inductive Operand
| Reg (r : Register)
| Pop
| Imm (i : Nat)

inductive Directive
| Mov (st : Operand × Operand)
| Add (st : Operand × Operand)
| Sub (st : Operand × Operand)
| Push (st : Operand)
