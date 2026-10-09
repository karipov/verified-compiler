inductive Register
| Rax
| Rcx

inductive Operand
| Reg (r : Register)
| Imm (i : Nat)

inductive Directive
| Mov (st : Operand × Operand)
| Add (st : Operand × Operand)
| Sub (st : Operand × Operand)
| Push (st : Operand)
| Pop (r : Register)
