inductive Register
| Rax
| Rcx

inductive Operand
| Reg (r : Register)
| Imm (i : Nat)

-- jumps don't use labels: `Jmp n` skips over the next `n` directives. (real x86 jumps are
-- relative too, they just count bytes instead of instructions.) the language has no loops,
-- so the compiler only ever needs to jump forwards.
inductive Directive
| Mov (st : Operand × Operand)
| Add (st : Operand × Operand)
| Sub (st : Operand × Operand)
| Push (st : Operand)
| Pop (r : Register)
| Cmp (st : Operand × Operand)
| Jmp (n : Nat)
| Je (n : Nat)  -- jump if equal (zero flag set)
| Jb (n : Nat)  -- jump if below (carry flag set)
