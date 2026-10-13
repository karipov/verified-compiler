import VerifiedCompiler.Ast

open Expr

-- random programs, for testing the real machine code against the interpreter (`tests/run.sh
-- --random N`). they're mostly well-typed, so that they get somewhere before failing, but now and
-- then an expression of the wrong type goes in to test the checks. functions only call the ones
-- defined before them, so every program finishes

structure Rng where
  seed : Nat

abbrev Gen := StateM Rng

-- a random number below `n`
def rand (n : Nat) : Gen Nat := do
  let s := ((← get).seed * 6364136223846793005 + 1442695040888963407) % 2 ^ 64
  set (Rng.mk s)
  return (s >>> 33) % max n 1

def pick {α : Type} [Inhabited α] (xs : List α) : Gen α := do
  return xs[← rand xs.length]!

inductive Ty
| num
| bool
| pair (a b : Ty)
deriving BEq, Inhabited

def randTy : Nat → Gen Ty
| 0 => do pick [Ty.num, Ty.bool]
| d + 1 => do
  match ← rand 4 with
  | 0 => return .pair (← randTy d) (← randTy d)
  | 1 => return .bool
  | _ => return .num

structure Sig where
  name : String
  params : List Ty
  ret : Ty
deriving Inhabited

-- what's in scope: variables and functions, with their types
structure Ctx where
  vars : List (String × Ty)
  fns : List Sig

def Ctx.varsOf (ctx : Ctx) (ty : Ty) : List String :=
  -- a shadowed variable has the type of its innermost binding
  (ctx.vars.filter fun (x, t) => t == ty && ctx.vars.lookup x == some t).map (·.1)

mutual
-- an expression of type `ty`, nested at most `d` deep
def genExpr (ctx : Ctx) (ty : Ty) : Nat → Gen Expr
| 0 => genLeaf ctx ty
| d + 1 => do
  -- sometimes, an expression of the wrong type
  if (← rand 25) == 0 then
    return ← genExpr ctx (← randTy 1) d
  match ← rand 10 with
  | 0 => return ← genLeaf ctx ty
  | 1 => return If (← genExpr ctx .bool d) (← genExpr ctx ty d) (← genExpr ctx ty d)
  | 2 =>
    let x := s!"x{← rand 6}"
    let t ← randTy 1
    return Let x (← genExpr ctx t d) (← genExpr { ctx with vars := (x, t) :: ctx.vars } ty d)
  | 3 =>
    let fns := ctx.fns.filter (·.ret == ty)
    if fns.isEmpty then return ← genLeaf ctx ty
    let f ← pick fns
    return App f.name (← genArgs ctx f.params d)
  | 4 =>
    let t ← randTy 1
    if (← rand 2) == 0 then return Left (← genExpr ctx (.pair ty t) d)
    else return Right (← genExpr ctx (.pair t ty) d)
  | _ =>
    match ty with
    | .num =>
      match ← rand 4 with
      | 0 => return Add1 (← genExpr ctx .num d)
      | 1 => return Sub1 (← genExpr ctx .num d)
      | 2 => return Expr.Add (← genExpr ctx .num d) (← genExpr ctx .num d)
      | _ => return Expr.Sub (← genExpr ctx .num d) (← genExpr ctx .num d)
    | .bool =>
      match ← rand 9 with
      | 0 => return IsZero (← genExpr ctx .num d)
      | 1 => return Lt (← genExpr ctx .num d) (← genExpr ctx .num d)
      | 2 => return Expr.Not (← genExpr ctx .bool d)
      | 3 =>
        let t ← pick [Ty.num, Ty.bool]
        return Expr.Eq (← genExpr ctx t d) (← genExpr ctx t d)
      | 4 => return Expr.And (← genExpr ctx .bool d) (← genExpr ctx .bool d)
      | 5 => return Expr.Or (← genExpr ctx .bool d) (← genExpr ctx .bool d)
      | 6 => return IsNum (← genExpr ctx (← randTy 1) d)
      | 7 => return IsBool (← genExpr ctx (← randTy 1) d)
      | _ => return IsPair (← genExpr ctx (← randTy 1) d)
    | .pair a b => return Expr.Pair (← genExpr ctx a d) (← genExpr ctx b d)

def genArgs (ctx : Ctx) : List Ty → Nat → Gen (List Expr)
| [], _ => return []
| t :: ts, d => return (← genExpr ctx t d) :: (← genArgs ctx ts d)

def genLeaf (ctx : Ctx) (ty : Ty) : Gen Expr := do
  let vars := ctx.varsOf ty
  if !vars.isEmpty && (← rand 2) == 0 then
    return Var (← pick vars)
  match ty with
  | .num => return Num (← rand 20)
  | .bool => return Expr.Bool ((← rand 2) == 0)
  | .pair a b => return Expr.Pair (← genLeaf ctx a) (← genLeaf ctx b)
end

def genProgram : Gen Program := do
  let mut fns : List Sig := []
  let mut defs : List Defn := []
  for i in [0:← rand 5] do
    let params ← (List.range (← rand 4)).mapM fun _ => randTy 1
    let ret ← randTy 1
    let names := (List.range params.length).map (s!"a{·}")
    let body ← genExpr ⟨names.zip params, fns⟩ ret 4
    fns := fns ++ [⟨s!"f{i}", params, ret⟩]
    defs := defs ++ [⟨s!"f{i}", names, body⟩]
  let main ← genExpr ⟨[], fns⟩ (← randTy 2) 5
  return ⟨defs, main⟩

def randomProgram (seed : Nat) : Program :=
  (genProgram.run ⟨seed⟩).1
