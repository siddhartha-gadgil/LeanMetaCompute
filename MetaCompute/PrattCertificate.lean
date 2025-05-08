import Mathlib
import MetaCompute.PowerMod
/-!
## Pratt primality test: Certificate

In this file, we define the structure of a Pratt certificate and the necessary lemmas to prove primality using the Lucas primality test.
-/

/--
Recover a number from its prime factorization, encoded as a list of pairs of primes and their powers.

The convention enforced here is that the exponents are one less than their actual value, as a way to enforce positivity.

For example, the number `2^3 * 3^2` would be represented as `[(2, 2), (3, 1)]`.
-/
def listProduct (l : List (Nat × Nat)) : Nat :=
  match l with
  | [] => 1
  | (x, y) :: xs =>
    let prod := listProduct xs
    let x_pow_y := x ^ (y + 1)
    x_pow_y * prod

theorem listProduct_nil : listProduct [] = 1 := by
  simp [listProduct]

theorem listProduct_cons (x : Nat × Nat) (xs : List (Nat × Nat)) :
  listProduct (x :: xs) = x.1 ^ (x.2 + 1) * listProduct xs := by
  simp [listProduct]

/-- An auxilliary tactic that proves a goal of the form
`∀ x ∈ (l : List α), P x` by creating one goal for each element of the list `l` and
  attempting to close each goal with the given tactic.
-/
macro "forall_in_list" tac:tactic : tactic => do
  `(tactic| (simp! only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; split_ands; all_goals (try $tac:tactic)))

open Parser Lean Meta Elab Tactic in
/-- A tactic to prove primality of small primes using `norm_num`. -/
elab "small_prime" max?:(num)? : tactic => withMainContext do
  let_expr Nat.Prime pE := ← getMainTarget | throwError "target is not of the form `Nat.Prime _`"
  let some p ← getNatValue? (← reduce pE) | throwError "Failed to obtain a natural number from {pE}"
  let max := max?.map (fun x => x.getNat) |>.getD 100
  if p < max then
    evalTactic <| ← `(tactic|norm_num)

/--
The information required for the Lucas primality test to certify primality.

Given the fields `a` and `factors`, the rest of the proofs can be synthesized automatically using the provided tactics.
-/
structure PrattCertificate (p : Nat) where
  a : Nat
  factors : List (Nat × Nat)
  p_ne_one : p ≠ 1 := by decide
  a_pow_pminus_1 : powerMod a (p - 1) p = 1 := by prove_power_mod
  factors_correct : listProduct factors = p - 1 := by decide
  a_pow_p_by_d_minus_1 : ∀ pair ∈ factors, powerMod a ((p - 1) / pair.1) p ≠  1 := by
    forall_in_list power_mod_neq
  factors_prime : ∀ pair ∈ factors, Nat.Prime pair.1 := by
    forall_in_list (set_option maxHeartbeats 100 in small_prime)


theorem List.prime_div_is_factor (l: List (Nat × Nat))
    (prod: listProduct l = n) (primes : ∀ pair ∈ l, Nat.Prime pair.1) :
    ∀ (q : ℕ), q ∣ n → Nat.Prime q →
      ∃ k : Nat, (q, k) ∈ l := by
  match l with
  | [] =>
    simp [listProduct] at prod
    intro q q_div_n prime_q
    simp [← prod] at q_div_n
    simp [q_div_n] at prime_q
    apply False.elim
    apply Nat.prime_one_false
    assumption
  | (q', m) :: xs =>
    intro q q_div_n prime_q
    simp [listProduct_cons] at prod
    simp [List.mem_cons]
    rw [← prod] at q_div_n
    rw [Nat.Prime.dvd_mul prime_q] at q_div_n
    if c: q = q' then
      rw [← c] at q_div_n
      simp [c]
    else
      cases c':q_div_n
      case inl d =>
        have d' := Nat.Prime.dvd_of_dvd_pow prime_q d
        have h' := primes (q', m) (by simp [List.mem_cons])
        simp at h'
        rw [Nat.prime_dvd_prime_iff_eq prime_q h'] at d'
        simp [c, d']
      case inr d =>
        let n' := listProduct xs
        let prod' : listProduct xs = n' := rfl
        let primes' : ∀ pair ∈ xs, Nat.Prime pair.1 := by
          intro pair h
          apply primes
          apply List.mem_cons_of_mem
          assumption
        let ih := List.prime_div_is_factor xs prod' primes' q d prime_q
        let ⟨k, factor⟩ := ih
        use k
        right
        assumption


theorem PrattCertificate.prime_dvd_is_factor {p : Nat} (cert : PrattCertificate p) :
  ∀ (q : ℕ), q ∣ p - 1 → Nat.Prime q →
    ∃ k : Nat, (q, k) ∈ cert.factors := by
  intro q q_div_pminus1 prime_q
  apply
    cert.factors.prime_div_is_factor cert.factors_correct cert.factors_prime q q_div_pminus1 prime_q

/-- A certificate can be used to prove primality by the Lucas primality test. -/
theorem pratt_certification (p : Nat) (cert : PrattCertificate p) : Nat.Prime p := by
  apply lucas_primality p cert.a
  · rw [← ZMod.natCast_mod]
    rw [← Nat.cast_pow]
    nth_rewrite 2 [← Nat.cast_one]
    rw [ZMod.natCast_eq_natCast_iff, Nat.ModEq]
    have h := cert.a_pow_pminus_1
    rw [powerModDef] at h
    rw [← Nat.pow_mod]
    rw [h]
    symm
    apply Nat.one_mod_eq_one.2
    exact cert.p_ne_one
  · intro q prime_q q_div_pminus1
    have h := cert.prime_dvd_is_factor q q_div_pminus1 prime_q
    have ⟨k, factor⟩ := h
    have h' := cert.a_pow_p_by_d_minus_1 (q, k) factor
    rw [powerModDef] at h'
    simp at h'
    rw [← ZMod.natCast_mod]
    rw [← Nat.cast_pow]
    nth_rewrite 2 [← Nat.cast_one]
    intro contra
    rw [ZMod.natCast_eq_natCast_iff, Nat.ModEq] at contra
    rw [← Nat.pow_mod] at contra
    rw [contra] at h'
    apply h'
    apply Nat.one_mod_eq_one.2
    exact cert.p_ne_one
