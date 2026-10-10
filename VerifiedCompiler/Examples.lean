import VerifiedCompiler.Compare

open Expr Value

-- some programs and what their compiled code gives. `correctness` already says the
-- interpreter gives the same thing, so these are just here to show what the answers are.
-- `#guard` runs them every time the project builds

def runCompiled (defs : List Defn) (main : Expr) (fuel : Nat := 1000) : Outcome Value :=
  Processor.evalToValue fuel (compile ⟨defs, main⟩)

-- (define (fact n) (if (zero? n) 1 (mul n (fact (sub1 n)))))
def fact : Defn := ⟨"fact", ["n"],
  If (IsZero (Var "n")) (Num 1) (App "mul" [Var "n", App "fact" [Sub1 (Var "n")]])⟩

-- (define (mul a b) (if (zero? a) 0 (+ b (mul (sub1 a) b))))
def mul : Defn := ⟨"mul", ["a", "b"],
  If (IsZero (Var "a")) (Num 0) (Expr.Add (Var "b") (App "mul" [Sub1 (Var "a"), Var "b"]))⟩

-- (define (range n) (if (zero? n) false (pair n (range (sub1 n)))))
def range : Defn := ⟨"range", ["n"],
  If (IsZero (Var "n")) (Expr.Bool false) (Expr.Pair (Var "n") (App "range" [Sub1 (Var "n")]))⟩

-- (define (sum l) (if (pair? l) (+ (left l) (sum (right l))) 0))
def sum : Defn := ⟨"sum", ["l"],
  If (IsPair (Var "l")) (Expr.Add (Left (Var "l")) (App "sum" [Right (Var "l")])) (Num 0)⟩

-- (define (loop x) (loop x))
def loop : Defn := ⟨"loop", ["x"], App "loop" [Var "x"]⟩

def defs : List Defn := [fact, mul, range, sum, loop]

-- functions and recursion
#guard runCompiled defs (App "fact" [Num 5]) == .done (Integer 120)
#guard runCompiled defs (App "sum" [App "range" [Num 10]]) == .done (Integer 55)
-- each call uses up one unit of fuel, so `(fact 5)` needs 7: one for each `fact` and the
-- deepest `mul` below them
#guard runCompiled defs (App "fact" [Num 5]) (fuel := 6) == .timeout
#guard runCompiled defs (App "fact" [Num 5]) (fuel := 7) == .done (Integer 120)
-- a program that runs forever runs out of fuel, however much it gets
#guard runCompiled defs (App "loop" [Num 1]) (fuel := 500) == .timeout

-- pairs
#guard runCompiled defs (App "range" [Num 2]) ==
  .done (Pair (Integer 2) (Pair (Integer 1) (Boolean false)))
#guard runCompiled defs (Let "p" (Expr.Pair (Num 1) (Num 2)) (Expr.Pair (Right (Var "p")) (Left (Var "p"))))
  == .done (Pair (Integer 2) (Integer 1))

-- errors: type errors, unbound variables, unknown functions, the wrong number of arguments
#guard runCompiled defs (Add1 (Expr.Bool true)) == .error
#guard runCompiled defs (Left (Num 3)) == .error
#guard runCompiled defs (Expr.Eq (Expr.Pair (Num 1) (Num 2)) (Num 1)) == .error
#guard runCompiled defs (Var "x") == .error
#guard runCompiled defs (App "nope" []) == .error
#guard runCompiled defs (App "fact" [Num 1, Num 2]) == .error

-- `And` and `Or` only look at e₂ when they have to
#guard runCompiled defs (Expr.And (Expr.Bool false) (App "loop" [Num 1])) == .done (Boolean false)
#guard runCompiled defs (Expr.Or (Expr.Bool false) (Num 3)) == .error

-- the other operators
#guard runCompiled defs (Expr.Not (Lt (Num 2) (Num 3))) == .done (Boolean false)
#guard runCompiled defs (Expr.Eq (Add1 (Num 2)) (Num 3)) == .done (Boolean true)
#guard runCompiled defs (IsNum (Expr.Bool true)) == .done (Boolean false)
#guard runCompiled defs (IsPair (Expr.Pair (Num 1) (Num 2))) == .done (Boolean true)
