inductive Expr
| Bool (b : Bool)
| Num (n : Nat)
| Add1 (e : Expr)
| Sub1 (e : Expr)

-- Add1 (Add1 (Sub1 (Add1 (Num 10)))) -> 12
-- 0101, 01010101, 10101 -> 12
