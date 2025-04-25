import MetaCompute.ParseFactors
import MetaCompute.PowerMod
import Mathlib

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

def factors (n : Nat) : IO <| List (Nat × Nat) := do
  let out ← queryPari s!"factor({n})"
  IO.ofExcept <| parseFactors|>.run out

def isPrime (n : Nat) : IO Bool := do
  let out ← queryPari s!"isprime({n})"
  return out = "1"

def znPrimRoot (p : Nat) : IO Nat := do
  let out ← queryPari s!"znprimroot({p})"
  let nStr := ((out.splitOn "(")[1]!.splitOn ",")[0]! |>.trim
  return nStr.toNat!

end pari
 open pari
-- #eval queryPari "isprime(85083351022467190124442353598696803287939269665617)"

-- #eval queryPari "factor(120)"

/-
"Mod(5, 85083351022467190124442353598696803287939269665617)"
-/
-- #eval queryPari "znprimroot(85083351022467190124442353598696803287939269665617)"

-- #eval isPrime 120
-- #eval factors 120

-- #check String.toNat?

#eval znPrimRoot 85083351022467190124442353598696803287939269665617 -- 5

def listProduct (l : List (Nat × Nat)) : Nat :=
  l.foldl (init := 1) (fun acc (x : Nat × Nat) => acc * x.1 ^ x.2)

structure PrattCertificate (p : Nat) where
  a : Nat
  a_pow_pminus_1 : powerMod a (p - 1) = 1
  factors : List (Nat × Nat)
  factors_correct : listProduct factors = p - 1
  a_pow_p_by_d_minus_1 : ∀ pair ∈ factors, powerMod a (p / pair.1) ≠  1
  factors_prime : ∀ pair ∈ factors, Nat.Prime pair.1

theorem PrattCertificate.prime_dvd_is_factor {p : Nat} (cert : PrattCertificate p) :
  ∀ (q : ℕ), q ∣ p - 1 → Nat.Prime q →
    ∃ k : Nat, (q, k) ∈ cert.factors := by
  sorry

/-
lucas_primality (p : ℕ) (a : ZMod p) (ha : a ^ (p - 1) = 1)
  (hd : ∀ (q : ℕ), Nat.Prime q → q ∣ p - 1 → a ^ ((p - 1) / q) ≠ 1) : Nat.Prime p
-/
#check lucas_primality

theorem pratt_certification (p : Nat) (cert : PrattCertificate p) : Nat.Prime p := by
  apply lucas_primality p cert.a
  · sorry
  · intro q prime_q q_div_pminus1
    have h := cert.prime_dvd_is_factor q q_div_pminus1 prime_q
    sorry

#check Int.ModEq.eq
