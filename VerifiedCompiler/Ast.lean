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
| Pair (e₁ : Expr) (e₂ : Expr)
| Left (e : Expr)
| Right (e : Expr)
| IsPair (e : Expr)  -- `pair?`
| App (f : String) (args : List Expr)
deriving Repr, BEq

-- `(define (name params...) body)`
structure Defn where
  name : String
  params : List String
  body : Expr
deriving Repr, BEq

-- some function definitions, then the expression to run
structure Program where
  defs : List Defn
  main : Expr
deriving Repr, BEq
