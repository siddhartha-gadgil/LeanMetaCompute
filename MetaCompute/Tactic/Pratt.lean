import MetaCompute.Pari
import MetaCompute.PrattCertificate

open Lean Elab Meta Term Tactic
open pari

def primeProp? (expr : Expr) : MetaM (Option Expr) := do
  let e ← mkFreshExprMVar (some <| mkConst ``Nat)
  let expr' ← mkAppM ``Nat.Prime #[e]
  if ← isDefEq expr expr' then
    return some e
  else
    return none


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


elab "pratt_step"  a:num ppSpace "[" fctrs:exp_pair,* "]" : tactic  => withMainContext do
  let a := a.getNat
  let factors ← fctrs.getElems.toList.mapM
    fun pair => fromExpPair pair
  let goals ← prattReduce a factors (← getMainGoal)
  replaceMainGoal goals

example : Nat.Prime 19 := by
  pratt_step 2 [ (2 ^ 1), (3 ^ 2) ]
  · decide
  · decide



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

#check prattImpl

example : Nat.Prime 85083351022467190124442353598696803287939269665617 := by
  · pratt_step 5 [(2^4), (3^1), (13^1), (47^1), (59^1), (547^1), (48527^1), (51347^1), (1019357^1),
      (35391418775811268295338933^1)]
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · pratt_step 2 [(2^1), (3^1), (7^1), (13^1)]
      · norm_num
      · norm_num
      · norm_num
      · norm_num
    · pratt_step 5 [(2^1), (19^1), (1277^1)]
      · norm_num
      · norm_num
      · pratt_step 2 [(2^2), (11^1), (29^1)]
        · norm_num
        · norm_num
        · norm_num
    · pratt_step 2 [(2^1), (25673^1)]
      · norm_num
      · pratt_step 3 [(2^3), (3209^1)]
        · norm_num
        · pratt_step 3 [(2^3), (401^1)]
          · norm_num
          · pratt_step 3 [(2^4), (5^2)]
            · norm_num
            · norm_num
    · pratt_step 2 [(2^2), (13^1), (19603^1)]
      · norm_num
      · norm_num
      · pratt_step 2 [(2^1), (3^4), (11^2)]
        · norm_num
        · norm_num
        · norm_num
    · pratt_step 2 [(2^2), (3^1), (1217^1), (16519^1), (43067977^1), (3406339441^1)]
      · norm_num
      · norm_num
      · pratt_step 3 [(2^6), (19^1)]
        · norm_num
        · norm_num
      · pratt_step 3 [(2^1), (3^1), (2753^1)]
        · norm_num
        · norm_num
        · pratt_step 3 [(2^6), (43^1)]
          · norm_num
          · norm_num
      · pratt_step 10 [(2^3), (3^1), (7^1), (269^1), (953^1)]
        · norm_num
        · norm_num
        · norm_num
        · pratt_step 2 [(2^2), (67^1)]
          · norm_num
          · norm_num
        · pratt_step 3 [(2^3), (7^1), (17^1)]
          · norm_num
          · norm_num
          · norm_num
      · pratt_step 11 [(2^4), (3^3), (5^1), (7^1), (225287^1)]
        · norm_num
        · norm_num
        · norm_num
        · norm_num
        · pratt_step 5 [(2^1), (112643^1)]
          · norm_num
          · pratt_step 2 [(2^1), (17^1), (3313^1)]
            · norm_num
            · norm_num
            · pratt_step 10 [(2^4), (3^2), (23^1)]
              · norm_num
              · norm_num
              · norm_num
