inductive Register
| Rax

inductive Operand
| Reg (r : Register)
| Imm (i : Nat)

inductive Directive
| Mov (st : Operand × Operand)
| Add (st : Operand × Operand)
| Sub (st : Operand × Operand)
