import VerifiedCompiler.Ast

open Expr

inductive Value
| Integer (i : Nat)
| Boolean (b : Bool)
| Pair (v₁ v₂ : Value)
deriving DecidableEq, Repr

open Value

-- how running a program can end: with an answer, with an error, or by running out of fuel.
-- fuel is used up by function calls, which are the only way a program can run forever
inductive Outcome (α : Type) where
| done (a : α)
| error
| timeout
deriving DecidableEq, Repr

instance : Monad Outcome where
  pure := .done
  bind r k :=
    match r with
    | .done a => k a
    | .error => .error
    | .timeout => .timeout

@[simp] theorem Outcome.done_bind {α β : Type} (a : α) (k : α → Outcome β) :
  (Outcome.done a >>= k) = k a := rfl

@[simp] theorem Outcome.error_bind {α β : Type} (k : α → Outcome β) :
  (Outcome.error >>= k) = .error := rfl

@[simp] theorem Outcome.timeout_bind {α β : Type} (k : α → Outcome β) :
  (Outcome.timeout >>= k) = .timeout := rfl

@[simp] theorem Outcome.pure_eq {α : Type} (a : α) : (pure a : Outcome α) = .done a := rfl

-- the type checks
def Value.asNum : Value → Outcome Nat
| Integer i => .done i
| _ => .error

def Value.asBool : Value → Outcome Bool
| Boolean b => .done b
| _ => .error

def Value.asPair : Value → Outcome (Value × Value)
| Pair v₁ v₂ => .done (v₁, v₂)
| _ => .error

-- `Eq` compares numbers and booleans. pairs live on the heap, so comparing them would mean
-- comparing pointers, which the interpreter has no notion of. that's an error instead
def Value.asAtom : Value → Outcome Value
| Pair _ _ => .error
| v => .done v

def Value.isNum : Value → Bool
| Integer _ => true
| _ => false

def Value.isBool : Value → Bool
| Boolean _ => true
| _ => false

def Value.isPair : Value → Bool
| Pair _ _ => true
| _ => false

-- the value of every variable in scope. `Let` puts its variable at the front, so it shadows
-- any outer variable with the same name
abbrev Env := List (String × Value)

def findDef (f : String) : List Defn → Option Defn
| [] => none
| d :: ds => if d.name = f then some d else findDef f ds

mutual
-- `fuel` is how many calls deep the program may go
def interp (defs : List Defn) (fuel : Nat) (env : Env) : Expr → Outcome Value
| Num n => pure (Integer n)
| Expr.Bool b => pure (Boolean b)
| Add1 e => do
  let i ← (← interp defs fuel env e).asNum
  pure (Integer (i + 1))
| Sub1 e => do
  let i ← (← interp defs fuel env e).asNum
  pure (Integer (i - 1))
| Expr.Add e₁ e₂ => do
  let i₁ ← (← interp defs fuel env e₁).asNum
  let i₂ ← (← interp defs fuel env e₂).asNum
  pure (Integer (i₁ + i₂))
| Expr.Sub e₁ e₂ => do
  let i₁ ← (← interp defs fuel env e₁).asNum
  let i₂ ← (← interp defs fuel env e₂).asNum
  pure (Integer (i₁ - i₂))
| IsZero e => do
  let i ← (← interp defs fuel env e).asNum
  pure (Boolean (decide (i = 0)))
| Lt e₁ e₂ => do
  let i₁ ← (← interp defs fuel env e₁).asNum
  let i₂ ← (← interp defs fuel env e₂).asNum
  pure (Boolean (decide (i₁ < i₂)))
-- only the branch that's taken gets evaluated
| If c t f => do
  let b ← (← interp defs fuel env c).asBool
  if b then interp defs fuel env t else interp defs fuel env f
| Expr.Not e => do
  let b ← (← interp defs fuel env e).asBool
  pure (Boolean (!b))
| Expr.Eq e₁ e₂ => do
  let v₁ ← (← interp defs fuel env e₁).asAtom
  let v₂ ← (← interp defs fuel env e₂).asAtom
  pure (Boolean (decide (v₁ = v₂)))
-- `And` and `Or` short-circuit: e₂ is only evaluated if e₁ doesn't already decide the answer
| Expr.And e₁ e₂ => do
  let b₁ ← (← interp defs fuel env e₁).asBool
  if b₁ then do
    let b₂ ← (← interp defs fuel env e₂).asBool
    pure (Boolean b₂)
  else pure (Boolean false)
| Expr.Or e₁ e₂ => do
  let b₁ ← (← interp defs fuel env e₁).asBool
  if b₁ then pure (Boolean true)
  else do
    let b₂ ← (← interp defs fuel env e₂).asBool
    pure (Boolean b₂)
| IsNum e => do
  let v ← interp defs fuel env e
  pure (Boolean v.isNum)
| IsBool e => do
  let v ← interp defs fuel env e
  pure (Boolean v.isBool)
| Var x =>
  match env.lookup x with
  | some v => pure v
  | none => .error
| Let x e body => do
  let v ← interp defs fuel env e
  interp defs fuel ((x, v) :: env) body
| Expr.Pair e₁ e₂ => do
  let v₁ ← interp defs fuel env e₁
  let v₂ ← interp defs fuel env e₂
  pure (Pair v₁ v₂)
| Left e => do
  let p ← (← interp defs fuel env e).asPair
  pure p.1
| Right e => do
  let p ← (← interp defs fuel env e).asPair
  pure p.2
| IsPair e => do
  let v ← interp defs fuel env e
  pure (Boolean v.isPair)
-- the arguments are evaluated first, then the call itself uses up one unit of fuel
| App f args =>
  match findDef f defs with
  | none => .error
  | some d =>
    if args.length = d.params.length then do
      let vs ← interpArgs defs fuel env args
      match fuel with
      | 0 => .timeout
      | fuel + 1 => interp defs fuel (d.params.zip vs) d.body
    else .error
termination_by e => (fuel, sizeOf e)

def interpArgs (defs : List Defn) (fuel : Nat) (env : Env) : List Expr → Outcome (List Value)
| [] => pure []
| e :: es => do
  let v ← interp defs fuel env e
  let vs ← interpArgs defs fuel env es
  pure (v :: vs)
termination_by es => (fuel, sizeOf es)
end

def interpret (fuel : Nat) (prog : Program) : Outcome Value :=
  interp prog.defs fuel [] prog.main
