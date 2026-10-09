inductive Expr
| Num (n : Nat)
| Bool (b : Bool)
| Add1 (e : Expr)
| Sub1 (e : Expr)
| Add (e₁ : Expr) (e₂ : Expr)
| Sub (e₁ : Expr) (e₂ : Expr)
| IsZero (e : Expr)
| Lt (e₁ : Expr) (e₂ : Expr)
| If (c : Expr) (t : Expr) (f : Expr)
| Not (e : Expr)
| Eq (e₁ : Expr) (e₂ : Expr)
| And (e₁ : Expr) (e₂ : Expr)
| Or (e₁ : Expr) (e₂ : Expr)
| IsNum (e : Expr)   -- `num?`
| IsBool (e : Expr)  -- `bool?`
| Var (x : String)
| Let (x : String) (e : Expr) (body : Expr)
