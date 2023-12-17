inductive Expr
| Num (n : Nat)
| Add1 (e : Expr)
| Sub1 (e : Expr)
| Add (e₁ : Expr) (e₂ : Expr)
