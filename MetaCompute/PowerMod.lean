import Mathlib
import Lean
import Qq

def powerMod (a b m : ℕ) : ℕ   :=
  if b = 0 then 1  % m
  else
  let r := b % 2
  if r = 0 then
    let n := powerMod a (b/2) m
    (n * n) % m
  else
    let n := powerMod a (b/2) m
    (a * n * n) % m
termination_by b

theorem zero_powerMod (a m : ℕ) : powerMod a 0 m = 1 % m :=
  by simp [powerMod]

theorem even_powerMod (a b m n : ℕ) :
  powerMod a b m = n → powerMod a (2 * b)  m = (n * n) % m := by
    intro hyp
    rw [powerMod]
    split
    · have h': 2 * b = 0 := by assumption
      simp at h'
      rw [powerMod] at hyp
      simp [h'] at hyp
      rw [← hyp, ← Nat.mul_mod]
    · simp
      rw [hyp]

theorem even_powerMod' (a b m : ℕ) : powerMod a (2 * b) m = ((powerMod a b m) ^ 2) % m := by
  rw [even_powerMod, pow_two]; rfl

theorem odd_powerMod (a b m n : ℕ) :
  powerMod a b m = n → powerMod a  (2 * b + 1)  m = (a * n * n) % m := by
    intro hyp
    rw [powerMod]
    have nz : ¬ (2 * b + 1 = 0) := by
      omega
    simp [nz]
    have h1 : (2 * b + 1) / 2 = b := by
      simp [Nat.add_div]
    simp [h1]
    rw [hyp]

theorem powerModDef (a b m: ℕ): powerMod a b m = a ^ b % m := by
  if c: b = 0 then
    simp [c, zero_powerMod]
  else
    if b % 2 = 0 then
      have h: b = 2 * (b / 2) := by
        rw [Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero (by assumption))]
      rw [h]
      have hyp := powerModDef a (b/2) m
      let lem := even_powerMod a (b/2) m _ hyp
      rw [lem]
      rw [two_mul, Nat.pow_add, Nat.mul_mod (a ^ (b/2))]
    else
      have h: b = 2 * (b / 2) + 1 := by
        let lem := Nat.div_add_mod b 2
        have c' : b % 2 = 1 := by
          cases Nat.mod_two_eq_zero_or_one b with
          | inl h => contradiction
          | inr h => assumption
        simp [c'] at lem
        rw [lem]
      rw [h]
      have hyp := powerModDef a (b/2) m
      let lem := odd_powerMod a (b/2) m _ hyp
      simp at lem
      rw [lem]
      rw [two_mul, Nat.pow_add, Nat.pow_add, pow_one, mul_assoc, mul_comm]
      simp [Nat.mul_mod, Nat.mod_mod]

theorem odd_powerMod' (a b m : ℕ) : powerMod a (b + 1) m = (a * powerMod a b m) % m := by
  rw [powerModDef, powerModDef, pow_succ, mul_comm _ a, Nat.mul_mod_mod]

open Lean Meta Elab Tactic Qq

/--
Expression for the equation `powerMod a b m = n`.
-/
def eqnExpr (a b m n : ℕ) : MetaM Expr := do
    let aExp := toExpr a
    let bExp := toExpr b
    let mExp := toExpr m
    let nExp := toExpr n
    let lhs ←  mkAppM ``powerMod #[aExp, bExp, mExp]
    mkEq lhs nExp

def eqnExpr? (e: Expr) : MetaM (Option (ℕ × ℕ × ℕ × ℕ)) := do
  let nat := mkConst ``Nat
  let aVar ← mkFreshExprMVar (some nat)
  let bVar ← mkFreshExprMVar (some nat)
  let mVar ← mkFreshExprMVar (some nat)
  let nVar ← mkFreshExprMVar (some nat)
  let lhs ← mkAppM ``powerMod #[aVar, bVar, mVar]
  let eq ← mkEq lhs nVar
  if ← isDefEq e eq then
    let aVar ← reduce aVar
    let bVar ← reduce bVar
    let mVar ← reduce mVar
    let nVar ← reduce nVar
    return match aVar, bVar, mVar, nVar with
      | ((Lean.Expr.lit (Lean.Literal.natVal a))), (Lean.Expr.lit (Lean.Literal.natVal b)), (Lean.Expr.lit (Lean.Literal.natVal m)), (Lean.Expr.lit (Lean.Literal.natVal n)) => some (a, b, m, n)
      | _, _, _, _ => none
  else
    return none

#check HPow.hPow

#check Lean.MVarId.isAssigned
simproc ↓ powerModIterSquare (powerMod _ _ _) := fun e ↦ do
  -- let some e ← checkTypeQ e q(ℕ) | return .continue
  -- let ~q(powerMod $a $b $m) := e | return .continue
  let_expr powerMod a b m := e | return .continue
  let some b ← getNatValue? b | return .continue
  let a : Q(ℕ) := a
  -- let some a ← Qq.checkTypeQ a q(ℕ) | return .continue
  let m : Q(ℕ) := m
  -- let some m ← Qq.checkTypeQ m q(ℕ) | return .continue
  if b = 0 then
    return .visit {
      expr := q(1 % $m),
      proof? := some q(zero_powerMod $a $m)
    }
  else if b % 2 = 0 then
    let b' : Q(ℕ) := toExpr (b / 2)
    return .visit {
      expr := q((powerMod $a $b' $m) ^ 2 % $m),
      proof? := some q(even_powerMod' $a $b' $m)
    }
  else
    let b' : Q(ℕ) := toExpr b.pred
    return .visit {
      expr := q(($a * powerMod $a $b' $m) % $m),
      proof? := some q(odd_powerMod' $a $b' $m)
    }

-- example : powerMod 5 9 3 = 2 := by
--   simp only [powerModIterSquare]
--   rfl

def powerModProof (a b m : ℕ) : MetaM Expr := do
  let n := powerMod a b m
  let goal ← eqnExpr a b m n
  let mvarId ← mkFreshMVarId
  let mvar ← mkFreshExprMVarWithId mvarId (some goal)
  if b = 0 then
    let expr ← (mkAppM ``zero_powerMod #[toExpr  a, toExpr  m])
    mvarId.assign expr
    return mkMVar mvarId
  else
    if b % 2 = 0 then
      let b' := b/2
      let n' := powerMod a (b/2) m
      let prevPf ← powerModProof a b' m
      let expr ← (mkAppM ``even_powerMod
        #[toExpr  a, toExpr  b', toExpr  m,
        toExpr  n', prevPf])
      mvarId.assign expr
      return mkMVar mvarId
    else
      let b' := b/2
      let n' := powerMod a (b/2) m
      let prevPf ← powerModProof a b' m
      let expr ← (mkAppM ``odd_powerMod
        #[toExpr  a, toExpr  b', toExpr  m,
        toExpr  n', prevPf])
      mvarId.assign expr
      return mkMVar mvarId

open Qq in
/--
Given a meta variable `mvarId`, assign to it a proof of the equation `powerMod a b m = n`.
-/
def provePowModM : MVarId → MetaM Unit :=
  fun mvarId =>
    mvarId.withContext do
    let goalType ← mvarId.getType
    let some tgt ← checkTypeQ goalType q(Prop) | throwError "prove_power_mod: expected the goal to be a proposition"
    let ~q(powerMod $a $b $m = $n) := tgt | throwError "prove_power_mod: expected the goal to be a powerMod equation"
    let pf ← powerModProof (← decodeNatExpr a) (← decodeNatExpr b) (← decodeNatExpr m)
    mvarId.assign pf
    return
where
  decodeNatExpr (e : Q(ℕ)) : MetaM ℕ := do
    let e ← reduce e
    let some val ← getNatValue? e | throwError "prove_power_mod: expected a natural number for {e}"
    return val

elab "prove_power_mod" : tactic => liftMetaFinishingTactic provePowModM

elab "power_mod_pf#"
    a:num "^" b:num "%" m:num  : term => do
    powerModProof a.getNat b.getNat m.getNat

elab "power_mod_pf#"
    a:num "^" "(" b':num "/" q:num ")" "%" m:num  : term => do
    let b := b'.getNat / q.getNat
    powerModProof a.getNat b m.getNat

#eval powerMod 2232421124 10027676 121 -- 45

example : 2232421124 ^ 10027676 % 121 = 45 := by
  decide +kernel

example : powerMod 2232421124 10027676 121 = 45 := by
  prove_power_mod

example : powerMod 2232421124 10027676 121 = 45 := by
  prove_power_mod


example : powerMod 2232421124 10027676 121 = 45 := by
  have := power_mod_pf# 2232421124 ^ 10027676 % 121
  rw [this]

example : ¬ powerMod 2232421124 10027676 121 = 41 := by
  have := power_mod_pf# 2232421124 ^ 10027676 % 121
  rw [this]
  simp

open Qq in
elab "power_mod_neq" : tactic => withMainContext do
  let tgt ← getMainTarget
  let some tgt ← checkTypeQ tgt q(Prop) | throwError "power_mod_neq: expected the goal to be a proposition"
  let ~q(powerMod $a ($b' / $q) $m ≠ $n) := tgt | throwError "power_mod_neq: expected the goal to be a powerMod in-equation"
  let delabNatExpr (e : Q(ℕ)) : MetaM NumLit := do
    let e ← reduce e
    let some val ← getNatValue? e | throwError "power_mod_neq: expected a natural number for {e}"
    return Syntax.mkNatLit val
  let a ← delabNatExpr a
  let b' ← delabNatExpr b'
  let q ← delabNatExpr q
  let m ← delabNatExpr m
  -- logInfo m!"power_mod_neq: {a} ^ ({b'} / {q}) % {m} ≠ {n}"
  let tac ← `(tactic|have := power_mod_pf# $a ^ ($b' / $q) % $m)
  let tacs := #[tac, ← `(tactic|rw [this]), ← `(tactic|decide)]
  let tacSeq ← `(tacticSeq| $tacs*)
  evalTactic =<< `(tactic| ($tacSeq))
