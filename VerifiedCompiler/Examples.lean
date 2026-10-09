import VerifiedCompiler.Compare

open Expr Value

-- some programs and what their compiled code gives. `correctness` already says the
-- interpreter gives the same thing, so these are just here to show what the answers are.
-- `#guard` runs them every time the project builds

-- type errors and unbound variables end in an error instead of garbage
#guard Processor.evalToValue (compile (Add1 (Expr.Bool true))) == none
#guard Processor.evalToValue (compile (If (Num 0) (Num 1) (Num 2))) == none
#guard Processor.evalToValue (compile (Var "x")) == none

-- variables
#guard Processor.evalToValue (compile (Let "x" (Num 5) (Expr.Add (Var "x") (Var "x"))))
  == some (Integer 10)
#guard Processor.evalToValue (compile (Let "x" (Num 1) (Let "x" (Expr.Bool true) (Var "x"))))
  == some (Boolean true)
-- x lives in slot 1 here, since slot 0 is holding the 1 while the `Let` runs
#guard Processor.evalToValue
    (compile (Expr.Add (Num 1) (Let "x" (Num 2) (Expr.Sub (Num 10) (Var "x")))))
  == some (Integer 9)

-- `And` and `Or` only look at e₂ when they have to
#guard Processor.evalToValue (compile (Expr.And (Expr.Bool false) (Var "y")))
  == some (Boolean false)
#guard Processor.evalToValue (compile (Expr.Or (Expr.Bool false) (Num 3))) == none

-- the other new operators
#guard Processor.evalToValue (compile (Expr.Not (Lt (Num 2) (Num 3)))) == some (Boolean false)
#guard Processor.evalToValue (compile (Expr.Eq (Num 3) (Expr.Bool true))) == some (Boolean false)
#guard Processor.evalToValue (compile (Expr.Eq (Add1 (Num 2)) (Num 3))) == some (Boolean true)
#guard Processor.evalToValue (compile (IsNum (Expr.Bool true))) == some (Boolean false)
#guard Processor.evalToValue (compile (IsBool (IsZero (Num 0)))) == some (Boolean true)
