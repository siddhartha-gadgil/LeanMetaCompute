import MetaCompute.Pari
import MetaCompute.PrattCertificate
/-!
## Pratt primality test: Tactic

This file implements the tactic `pratt` for proving primality of a number using the Pratt primality test.
-/
open Lean Elab Meta Term Tactic
open pari

def primeProp? (expr : Expr) : MetaM (Option Expr) := do
  let e ← mkFreshExprMVar (some <| mkConst ``Nat)
  let expr' ← mkAppM ``Nat.Prime #[e]
  if ← isDefEq expr expr' then
    return some e
  else
    return none

/--
Given a goal of the form `Nat.Prime p`, this function reduces the goal to proving primality of smaller numbers as required by Pratt certificates for Lucas Primality.
-/
def prattReduce (a : ℕ) (factors : List (ℕ × ℕ)) (goal : MVarId)  : MetaM <| List MVarId := goal.withContext do
  let some pE  ← primeProp? (←   goal.getType) | throwError "target is not of the form `Nat.Prime _`"
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
  let (goals, _) ←  runTactic factors_prime <| ← `(tactic| (simp! only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; split_ands))
  let fullCert ←  mkAppM ``PrattCertificate.mk (#[toExpr a, toExpr factors] ++ (args.toArray.map mkMVar))
  let primeProof ← mkAppM ``pratt_certification #[pE, fullCert]
  goal.assign primeProof
  return goals

open Lean Elab Meta Term
declare_syntax_cat exp_pair
syntax "(" num "^" num ")" : exp_pair
def fromExpPair : Syntax → MetaM (ℕ × ℕ)
| `(exp_pair|( $a ^ $b)) => return (a.getNat, b.getNat)
| _ => throwUnsupportedSyntax

def toExpPair (pair : ℕ × ℕ) : MetaM <| TSyntax `exp_pair :=
  let aStx := Syntax.mkNumLit (toString pair.1)
  let bStx := Syntax.mkNumLit (toString pair.2)
  `(exp_pair| ( $aStx ^ $bStx))

/--
The `pratt_step` tactic is used to prove primality of a number by reducing it to smaller numbers as required by Pratt certificates for Lucas Primality.
-/
elab "pratt_step"  a:num ppSpace "[" fctrs:exp_pair,* "]" : tactic  => withMainContext do
  let a := a.getNat
  let factors ← fctrs.getElems.toList.mapM
    fun pair => fromExpPair pair
  let goals ← prattReduce a factors (← getMainGoal)
  replaceMainGoal goals

/--
Generate a proof script for the `pratt` tactic.
-/
partial def primeScript (goal : MVarId) :
  MetaM <| List Syntax.Tactic := goal.withContext do
  let tgt ← reduce (← goal.getType)
  let some pE :=  ← primeProp? tgt | throwError s!"target {← ppExpr tgt} ({tgt}) is not of the form `Nat.Prime _`"
  let some p ← getNatValue? (← reduce pE) | throwError "Failed to obtain a natural number from {pE}"
  if p < 100 then
    unless Nat.Prime p do
      throwError "{pE} is not a prime"
    discard <| runTactic goal <| ← `(tactic|norm_num)
    return [← `(tactic|norm_num)]
  else
    unless ← ping do
      throwError "Pari (https://pari.math.u-bordeaux.fr/) is not installed or not in the PATH. This is required for `pratt`."
    let check ← queryPari s!"isprime({p})"
    unless check = "1" do
      throwError "{pE} is not a prime (according to Pari)"
    let a ← znPrimRoot p
    -- logInfo m!"Primitive root: {a}"
    let factors := (← factors (p - 1))
    -- logInfo m!"Factors: {factors}"
    let newGoals ← prattReduce a factors goal
    let aStx := Syntax.mkNumLit (toString a)
    let factorStxs ←  factors.mapM (fun (x : Nat × Nat) => toExpPair x)
    let factorStxs := factorStxs.toArray
    let head ← `(tactic|pratt_step $aStx [$factorStxs,*])
    let tail ← newGoals.mapM fun goal => do
      let stx ← primeScript goal
      let stx := stx.toArray
      `(tactic| · $stx*)
    return head :: tail

declare_syntax_cat computer_algebra_system
syntax "pari" : computer_algebra_system

/--
The `pratt` tactic is used to prove primality of a number using the Pratt primality test.
It works by reducing the goal to proving primality of smaller numbers as required by Pratt certificates for Lucas Primality.
The tactic uses the `pratt_step` command to prove primality of a number by reducing it to smaller numbers.

A code action allows you to generate the proof script for the `pratt` tactic, so that calls to pari-gp are not required for the generated script.
-/
syntax (name := pratt_tac) "pratt" (computer_algebra_system)? : tactic

@[tactic pratt_tac]
def prattImpl : Tactic := fun stx => withMainContext do
  match stx with
  | `(tactic|pratt)
  | `(tactic| pratt pari) => withMainContext do
    let scripts ←  primeScript (← getMainGoal)
    let scripts := scripts.toArray
    TryThis.addSuggestion stx <| ← `(tactic|· $scripts*)
    return
  | _ =>
    throwUnsupportedSyntax
