import MetaCompute.Parsers
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
  getFactors <| ← queryPari s!"factor({n})"

def isPrime (n : Nat) : IO Bool := do
  let out ← queryPari s!"isprime({n})"
  return out = "1"

def znPrimRoot (p : Nat) : IO Nat := do
  getPrimitiveRootOf p <| ← queryPari s!"znprimroot({p})"

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

macro "forall_in_list" tac:tactic : tactic => do
  `(tactic| (simp! only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; split_ands; all_goals (try $tac:tactic)))

open Parser Lean Meta Elab Tactic in
elab "small_prime" max?:(num)? : tactic => withMainContext do
  let_expr Nat.Prime pE := ← getMainTarget | throwError "target is not of the form `Nat.Prime _`"
  let some p ← getNatValue? (← reduce pE) | throwError "Failed to obtain a natural number from {pE}"
  let max := max?.map (fun x => x.getNat) |>.getD 100
  if p < max then
    evalTactic <| ← `(tactic|norm_num)

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

#count_heartbeats in
example : PrattCertificate 48611 := {
  a := 2,
  factors := [(2, 0), (5, 0), (4861, 0)],
  factors_prime := by
    forall_in_list norm_num
}


example : ∀ n ∈ [7, 3, 5], Nat.Prime n := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  split_ands
  all_goals norm_num


#check or_imp

open Lean Elab Meta Term Tactic

unsafe def Lean.Expr.applyAutoParamArgs (e : Expr) : TacticM Expr := do
  let (mvars, _, _) ← forallMetaTelescope (← inferType e)
  for mvar in mvars do
    if let .app (.app (.const ``autoParam _) α) val ← inferType mvar then do
      let stx ← evalExpr Syntax (mkConst ``Syntax) val
      if stx.isOfKind `term then
        discard <| isDefEq mvar (← Term.elabTerm stx α)
      else if stx.isOfKind `tactic || stx.isOfKind ``Parser.Tactic.tacticSeq then
        let goals ← Tactic.run mvar.mvarId! (evalTactic stx)
        appendGoals goals
      else
        logWarning m!"Unknown syntax kind {stx.getKind} of {stx}"
  let mvars : Array Expr ← mvars.mapM instantiateMVars
  let e := mkAppN e mvars
  mkLambdaFVars (mvars.filter Expr.isMVar) e

/-- Apply the given arguments to the declaration with name `constName` and
    synthesize as many of the remaining arguments as possible using the `autoParam` information. -/
unsafe def Lean.Meta.Expr.mkAppAutoM (constName : Name) (args : Array Expr) : TacticM Expr := do
  mkAppN (mkConst constName) args |>.applyAutoParamArgs

open Lean Elab Meta Term
declare_syntax_cat exp_pair
syntax "(" num "^" num ")" : exp_pair
def fromExpPair : Syntax → MetaM (ℕ × ℕ)
| `(exp_pair|( $a ^ $b)) => return (a.getNat, b.getNat)
| _ => throwUnsupportedSyntax

elab "pratt_certificate_for_safe%" p:num "using" a:num : term => do
  let pExpr ← elabTerm p (mkConst ``Nat)
  let tgt ← mkAppM ``PrattCertificate #[pExpr]
  let goal ← mkFreshExprMVar (some tgt)
  let p := p.getNat
  let a := a.getNat
  let factors ← factors (p - 1)
  let factors := factors.map (fun (x : Nat × Nat) => (x.1, x.2 - 1))
  let cert := mkApp3 (mkConst ``PrattCertificate.mk) (toExpr p) (toExpr a) (toExpr factors)
  let [p_ne_one, a_pow_minus_one, factors_correct, a_pow_d_by_pminus1, factors_prime] ← goal.mvarId!.apply cert | throwError
    "pratt_certificate_for_safe%: expected 5 arguments"
  discard <| runTactic p_ne_one <| ← `(tactic|decide)
  discard <| runTactic a_pow_minus_one <| ← `(tactic|prove_power_mod)
  discard <| runTactic factors_correct <| ← `(tactic|decide)
  discard <| runTactic a_pow_d_by_pminus1 <| ← `(tactic|forall_in_list power_mod_neq)
  discard <| runTactic factors_prime <| ← `(tactic|simp +decide only)
  return goal

#eval pratt_certificate_for_safe% 19 using 2

-- For experiments only, purge later
elab "pratt_certificate_safe%" p:num "using" a:num "[" fctrs:exp_pair,* "]" : term => do
  let pExpr ← elabTerm p (mkConst ``Nat)
  let tgt ← mkAppM ``PrattCertificate #[pExpr]
  let goal ← mkFreshExprMVar (some tgt)
  let p := p.getNat
  let a := a.getNat
  let factors ← fctrs.getElems.toList.mapM
    fun pair => fromExpPair pair
  let factors := factors.map (fun (x : Nat × Nat) => (x.1, x.2 - 1))
  let cert := mkApp3 (mkConst ``PrattCertificate.mk) (toExpr p) (toExpr a) (toExpr factors)
  let [p_ne_one, a_pow_minus_one, factors_correct, a_pow_d_by_pminus1, factors_prime] ← goal.mvarId!.apply cert | throwError
    "pratt_certificate_for_safe%: expected 5 arguments"
  discard <| runTactic p_ne_one <| ← `(tactic|decide)
  discard <| runTactic a_pow_minus_one <| ← `(tactic|prove_power_mod)
  discard <| runTactic factors_correct <| ← `(tactic|decide)
  discard <| runTactic a_pow_d_by_pminus1 <| ← `(tactic|forall_in_list power_mod_neq)
  discard <| runTactic factors_prime <| ← `(tactic|simp +decide only)
  return goal

#eval pratt_certificate_safe% 19 using 2 [ (2 ^ 1), (3 ^ 2) ]


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

#check Nat.Prime.dvd_of_dvd_pow

#check Nat.Prime.dvd_mul
#check Nat.prime_one_false
#check Nat.prime_dvd_prime_iff_eq

#check List.foldl_cons

theorem PrattCertificate.prime_dvd_is_factor {p : Nat} (cert : PrattCertificate p) :
  ∀ (q : ℕ), q ∣ p - 1 → Nat.Prime q →
    ∃ k : Nat, (q, k) ∈ cert.factors := by
  intro q q_div_pminus1 prime_q
  apply
    cert.factors.prime_div_is_factor cert.factors_correct cert.factors_prime q q_div_pminus1 prime_q

/-
lucas_primality (p : ℕ) (a : ZMod p) (ha : a ^ (p - 1) = 1)
  (hd : ∀ (q : ℕ), Nat.Prime q → q ∣ p - 1 → a ^ ((p - 1) / q) ≠ 1) : Nat.Prime p
-/
#check lucas_primality

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

elab "prime" : tactic => unsafe withMainContext do
  let_expr Nat.Prime pE := ← getMainTarget | throwError "target is not of the form `Nat.Prime _`"
  let some p ← getNatValue? (← reduce pE) | throwError "Failed to obtain a natural number from {pE}"
  let check ← queryPari s!"isprime({p})"
  unless check = "1" do
    throwError "{pE} is not a prime (according to Pari)"
  let a ← znPrimRoot p
  logInfo m!"Primitive root: {a}"
  let factors := (← factors (p - 1)) |>.map fun (q, e) ↦ (q, e - 1)
  logInfo m!"Factors: {factors}"
  let cert ← Expr.mkAppAutoM ``PrattCertificate.mk #[pE, toExpr a, toExpr factors]
  let primeProof ← mkAppM ``pratt_certification #[pE, cert]
  (← getMainGoal).assignIfDefEq primeProof
  pruneSolvedGoals

example : Nat.Prime 48611 := by
  prime
  · prime

def prattReduce (a : ℕ) (factors : List (ℕ × ℕ)) (goal : MVarId)  : MetaM <| List MVarId := goal.withContext do
  let_expr Nat.Prime pE := ←  goal.getType | throwError "target is not of the form `Nat.Prime _`"
  let some p ← getNatValue? (← reduce pE) | throwError "Failed to obtain a natural number from {pE}"
  let tgt ← mkAppM ``PrattCertificate #[pE]
  let prattGoal ← mkFreshExprMVar (some tgt)
  let factors := factors.map (fun (x : Nat × Nat) => (x.1, x.2 - 1))
  let cert := mkApp3 (mkConst ``PrattCertificate.mk) (toExpr p) (toExpr a) (toExpr factors)
  let args ← prattGoal.mvarId!.apply cert
  let [p_ne_one, a_pow_minus_one, factors_correct, a_pow_d_by_pminus1, factors_prime] := args | throwError
    "pratt_certificate: expected 5 arguments"
  discard <| runTactic p_ne_one <| ← `(tactic|decide)
  discard <| runTactic a_pow_minus_one <| ← `(tactic|prove_power_mod)
  discard <| runTactic factors_correct <| ← `(tactic|decide)
  discard <| runTactic a_pow_d_by_pminus1 <| ← `(tactic|forall_in_list power_mod_neq)
  let (goals, _) ←  runTactic factors_prime <| ← `(tactic| forall_in_list skip)
  let fullCert ←  mkAppM ``PrattCertificate.mk (#[toExpr a, toExpr factors] ++ (args.toArray.map mkMVar))
  let primeProof ← mkAppM ``pratt_certification #[pE, fullCert]
  goal.assign primeProof
  return goals


elab "pratt_step"  a:num "[" fctrs:exp_pair,* "]" : tactic => withMainContext do
  let a := a.getNat
  let factors ← fctrs.getElems.toList.mapM
    fun pair => fromExpPair pair
  let goals ← prattReduce a factors (← getMainGoal)
  replaceMainGoal goals

example : Nat.Prime 19 := by
  pratt_step 2 [ (2 ^ 1), (3 ^ 2) ]
  · decide
  · decide


example : Nat.Prime 85083351022467190124442353598696803287939269665617 := by repeat prime

#check Nat.one_mod_eq_one

#check Int.ModEq.eq
#check Nat.ModEq.eq_1

#check ZMod.intCast_eq_intCast_iff
#check Nat.cast_one

#check ZMod.natCast_eq_natCast_iff
