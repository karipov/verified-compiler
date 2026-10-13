inductive Register
| Rax
| Rcx
| R8
| R15  -- the heap pointer: where the next pair goes
deriving Repr, BEq

inductive Operand
| Reg (r : Register)
| Imm (i : Nat)
deriving Repr, BEq

-- jumps don't use labels: `Jmp n` skips over the next `n` directives. (real x86 jumps are
-- relative too, they just count bytes instead of instructions.) the compiler only ever jumps
-- forwards; the only way back is returning from a function.
inductive Directive
| Mov (st : Operand × Operand)
| Add (st : Operand × Operand)
| Sub (st : Operand × Operand)  -- stops at 0, like subtraction on `Nat`
| And (st : Operand × Operand)  -- bitwise and, used to pick out the tag bits of a value
| Push (st : Operand)
| Pop (r : Register)
| Load (k : Nat)                -- `mov rax, [rsp + 8 * k]`: the `k`th value down the stack
| LoadMem (dst base : Register) (off : Nat)   -- `mov dst, [base + off]`
| StoreMem (base : Register) (off : Nat) (src : Register)  -- `mov [base + off], src`
| Cmp (st : Operand × Operand)
| Jmp (n : Nat)
| Je (n : Nat)   -- jump if equal (zero flag set)
| Jne (n : Nat)  -- jump if not equal
| Jb (n : Nat)   -- jump if below (carry flag set)
| Call (f : String)
| Ret
| Drop (n : Nat)  -- `add rsp, 8 * n`: throw away the top `n` values on the stack
| Error           -- call the runtime's error handler, which never returns
deriving Repr, BEq
