import VerifiedCompiler.Parse
import VerifiedCompiler.Emit
import VerifiedCompiler.Process
import VerifiedCompiler.Gen

-- `vc run FILE` interprets a program, `vc model FILE` runs its compiled code on the processor
-- from `Process.lean`, and `vc asm FILE` prints its compiled code as x86-64 assembly. `run` and
-- `model` print "error" and exit with 1 when the program has an error, like the runtime does.
-- `vc gen SEED` prints a random program

-- how many calls deep a program may go. the real processor has no fuel: a program that runs
-- forever there runs out of stack instead
def fuel : Nat := 100000

def usage : String :=
  "usage: vc (run | model | asm) FILE\n       vc gen SEED"

def report (r : Outcome Value) : IO UInt32 := do
  IO.println r.toString
  match r with
  | .done _ => return 0
  | .error => return 1
  | .timeout => return 3

def main (args : List String) : IO UInt32 := do
  match args with
  | ["gen", seed] =>
    IO.println (randomProgram seed.toNat!).toString
    return 0
  | [cmd, file] =>
    let src ← IO.FS.readFile file
    match parseProgram src with
    | .error e =>
      IO.eprintln s!"{file}: {e}"
      return 2
    | .ok prog =>
      match cmd with
      | "run" => report (interpret fuel prog)
      | "model" => report (Processor.evalToValue fuel (compile prog))
      | "asm" =>
        match emit (compile prog) with
        | .ok asm =>
          IO.print asm
          return 0
        | .error e =>
          IO.eprintln s!"{file}: {e}"
          return 2
      | _ =>
        IO.eprintln usage
        return 2
  | _ =>
    IO.eprintln usage
    return 2
