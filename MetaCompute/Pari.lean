import MetaCompute.Parsers
import MetaCompute.PowerMod
import Mathlib
/-!
## Pari interface
This file provides an interface to the Pari library for primality testing and factorization.
It includes functions for checking primality, finding primitive roots, and factorization.
-/

open IO.Process in -- code by Max Nowak from https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/external.20process/near/345090183
/-- Pipe input into stdin of the spawned process, then return output upon completion. -/
def cmd_with_stdin (args : SpawnArgs) (input : String) : IO Output := do
  let child <- spawn { args with stdin := .piped, stdout := .piped, stderr := .piped }
  let (stdin, child) <- child.takeStdin
  stdin.putStr input
  stdin.flush
  let stdout <- IO.asTask child.stdout.readToEnd Task.Priority.dedicated
  let stderr <- child.stderr.readToEnd
  let exitCode <- child.wait
  let stdout <- IO.ofExcept stdout.get
  return { exitCode, stdout, stderr }

def queryPari (cmd : String) : IO String := do
  let out ← cmd_with_stdin
              { cmd := "gp", args := #["-q", "--emacs"]} cmd
  return out.stdout.trim

namespace pari

def ping : IO Bool := do
  let out ← cmd_with_stdin
              { cmd := "gp", args := #["-q", "--emacs"]} "version()"
  return out.exitCode == 0

def factors (n : Nat) : IO <| List (Nat × Nat) := do
  getFactors <| ← queryPari s!"factor({n})"

def isPrime (n : Nat) : IO Bool := do
  let out ← queryPari s!"isprime({n})"
  return out = "1"

def znPrimRoot (p : Nat) : IO Nat := do
  getPrimitiveRootOf p <| ← queryPari s!"znprimroot({p})"

end pari
open pari
