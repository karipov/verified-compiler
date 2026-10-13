import VerifiedCompiler.Ast
import VerifiedCompiler.Interpret

open Expr Value

-- programs are written as s-expressions, like in cs1260:
--
--   (define (fact n)
--     (if (zero? n) 1 (mul n (fact (sub1 n)))))
--   (fact 5)
--
-- every form but the last is a `define`, and the last one is the expression to run. comments
-- start with `;` and go to the end of the line

inductive SExp
| atom (s : String)
| list (xs : List SExp)
deriving Repr, BEq, Inhabited

/- ## Reading s-expressions -/

-- splits the source into parentheses and atoms. `cur` is the atom being read
def tokenize (s : String) : List String :=
  go s.toList "" false []
where
  flush (cur : String) (acc : List String) : List String :=
    if cur.isEmpty then acc else cur :: acc
  go : List Char → String → Bool → List String → List String
  | [], cur, _, acc => (flush cur acc).reverse
  | c :: cs, cur, true, acc => go cs cur (c != '\n') acc  -- inside a comment
  | c :: cs, cur, false, acc =>
    if c = '(' || c = ')' then go cs "" false (c.toString :: flush cur acc)
    else if c = ';' then go cs "" true (flush cur acc)
    else if c.isWhitespace then go cs "" false (flush cur acc)
    else go cs (cur.push c) false acc

-- `n` bounds how deeply the reader can recurse, so that it obviously stops. two calls per token
-- is plenty
mutual
def readSExp : Nat → List String → Except String (SExp × List String)
| 0, _ => .error "too deeply nested"
| _, [] => .error "unexpected end of input"
| n + 1, "(" :: ts => do
  let (xs, rest) ← readList n ts
  pure (.list xs, rest)
| _, ")" :: _ => .error "unexpected `)`"
| _, t :: ts => pure (.atom t, ts)

def readList : Nat → List String → Except String (List SExp × List String)
| 0, _ => .error "too deeply nested"
| _, [] => .error "missing `)`"
| _, ")" :: ts => pure ([], ts)
| n + 1, ts => do
  let (x, rest) ← readSExp n ts
  let (xs, rest) ← readList n rest
  pure (x :: xs, rest)
end

def readAll (ts : List String) : Except String (List SExp) :=
  go (2 * ts.length + 2) ts
where
  go : Nat → List String → Except String (List SExp)
  | _, [] => pure []
  | 0, _ => .error "too deeply nested"
  | n + 1, ts => do
    let (x, rest) ← readSExp (2 * ts.length + 2) ts
    let xs ← go n rest
    pure (x :: xs)

/- ## From s-expressions to programs -/

def keywords : List String :=
  ["add1", "sub1", "+", "-", "zero?", "<", "if", "not", "=", "and", "or", "num?", "bool?",
   "let", "pair", "left", "right", "pair?", "define", "true", "false"]

def isNumber (s : String) : Bool :=
  !s.isEmpty && s.all Char.isDigit

def isName (s : String) : Bool :=
  !s.isEmpty && !isNumber s && !keywords.contains s && !s.any (fun c => c = '(' || c = ')')

mutual
def parseExpr : SExp → Except String Expr
| .atom "true" => pure (Expr.Bool true)
| .atom "false" => pure (Expr.Bool false)
| .atom s =>
  if isNumber s then pure (Num s.toNat!)
  else if isName s then pure (Var s)
  else .error s!"unexpected `{s}`"
| .list [.atom "add1", e] => do pure (Add1 (← parseExpr e))
| .list [.atom "sub1", e] => do pure (Sub1 (← parseExpr e))
| .list [.atom "+", e₁, e₂] => do pure (Expr.Add (← parseExpr e₁) (← parseExpr e₂))
| .list [.atom "-", e₁, e₂] => do pure (Expr.Sub (← parseExpr e₁) (← parseExpr e₂))
| .list [.atom "zero?", e] => do pure (IsZero (← parseExpr e))
| .list [.atom "<", e₁, e₂] => do pure (Lt (← parseExpr e₁) (← parseExpr e₂))
| .list [.atom "if", c, t, f] => do pure (If (← parseExpr c) (← parseExpr t) (← parseExpr f))
| .list [.atom "not", e] => do pure (Expr.Not (← parseExpr e))
| .list [.atom "=", e₁, e₂] => do pure (Expr.Eq (← parseExpr e₁) (← parseExpr e₂))
| .list [.atom "and", e₁, e₂] => do pure (Expr.And (← parseExpr e₁) (← parseExpr e₂))
| .list [.atom "or", e₁, e₂] => do pure (Expr.Or (← parseExpr e₁) (← parseExpr e₂))
| .list [.atom "num?", e] => do pure (IsNum (← parseExpr e))
| .list [.atom "bool?", e] => do pure (IsBool (← parseExpr e))
| .list [.atom "let", .list [.list [.atom x, e]], body] =>
  if isName x then do pure (Let x (← parseExpr e) (← parseExpr body))
  else .error s!"can't bind `{x}`"
| .list [.atom "pair", e₁, e₂] => do pure (Expr.Pair (← parseExpr e₁) (← parseExpr e₂))
| .list [.atom "left", e] => do pure (Left (← parseExpr e))
| .list [.atom "right", e] => do pure (Right (← parseExpr e))
| .list [.atom "pair?", e] => do pure (IsPair (← parseExpr e))
| .list (.atom f :: args) =>
  if isName f then do pure (App f (← parseArgs args))
  else .error s!"bad `{f}` expression"
| .list _ => .error "expected an expression"

def parseArgs : List SExp → Except String (List Expr)
| [] => pure []
| e :: es => do pure ((← parseExpr e) :: (← parseArgs es))
end

def parseParam : SExp → Except String String
| .atom p => if isName p then pure p else .error s!"bad parameter `{p}`"
| .list _ => .error "bad parameter"

def parseDefn : SExp → Except String Defn
| .list [.atom "define", .list (.atom name :: params), body] =>
  if isName name then do
    pure ⟨name, ← params.mapM parseParam, ← parseExpr body⟩
  else .error s!"can't define `{name}`"
| _ => .error "expected `(define (name params...) body)`"

def parseProgram (src : String) : Except String Program := do
  let forms ← readAll (tokenize src)
  match forms.reverse with
  | [] => .error "empty program"
  | main :: defs => pure ⟨← defs.reverse.mapM parseDefn, ← parseExpr main⟩

/- ## Printing -/

def SExp.toString : SExp → String
| .atom s => s
| .list xs => "(" ++ " ".intercalate (xs.map SExp.toString) ++ ")"

mutual
def Expr.toSExp : Expr → SExp
| Num n => .atom (toString n)
| Expr.Bool b => .atom (if b then "true" else "false")
| Add1 e => .list [.atom "add1", e.toSExp]
| Sub1 e => .list [.atom "sub1", e.toSExp]
| Expr.Add e₁ e₂ => .list [.atom "+", e₁.toSExp, e₂.toSExp]
| Expr.Sub e₁ e₂ => .list [.atom "-", e₁.toSExp, e₂.toSExp]
| IsZero e => .list [.atom "zero?", e.toSExp]
| Lt e₁ e₂ => .list [.atom "<", e₁.toSExp, e₂.toSExp]
| If c t f => .list [.atom "if", c.toSExp, t.toSExp, f.toSExp]
| Expr.Not e => .list [.atom "not", e.toSExp]
| Expr.Eq e₁ e₂ => .list [.atom "=", e₁.toSExp, e₂.toSExp]
| Expr.And e₁ e₂ => .list [.atom "and", e₁.toSExp, e₂.toSExp]
| Expr.Or e₁ e₂ => .list [.atom "or", e₁.toSExp, e₂.toSExp]
| IsNum e => .list [.atom "num?", e.toSExp]
| IsBool e => .list [.atom "bool?", e.toSExp]
| Var x => .atom x
| Let x e body => .list [.atom "let", .list [.list [.atom x, e.toSExp]], body.toSExp]
| Expr.Pair e₁ e₂ => .list [.atom "pair", e₁.toSExp, e₂.toSExp]
| Left e => .list [.atom "left", e.toSExp]
| Right e => .list [.atom "right", e.toSExp]
| IsPair e => .list [.atom "pair?", e.toSExp]
| App f args => .list (.atom f :: Expr.argsToSExp args)

def Expr.argsToSExp : List Expr → List SExp
| [] => []
| e :: es => e.toSExp :: Expr.argsToSExp es
end

def Defn.toSExp (d : Defn) : SExp :=
  .list [.atom "define", .list (.atom d.name :: d.params.map .atom), d.body.toSExp]

def Program.toString (p : Program) : String :=
  "\n".intercalate ((p.defs.map Defn.toSExp ++ [p.main.toSExp]).map SExp.toString)

-- how answers are printed, here and by the runtime in `runtime/runtime.c`
def Value.toString : Value → String
| Integer n => s!"{n}"
| Boolean b => if b then "true" else "false"
| Pair v₁ v₂ => s!"(pair {v₁.toString} {v₂.toString})"

def Outcome.toString : Outcome Value → String
| .done v => v.toString
| .error => "error"
| .timeout => "timeout"
