import Mathlib
import Lean

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

theorem odd_powerMod (a b m n : ℕ) :
  powerMod a b m = n → powerMod a  (2 * b + 1)  m = (a * n * n) % m := by
    intro hyp
    rw [powerMod]
    have nz : ¬ (2 * b + 1 = 0) := by
      intro h
      simp at h
    simp [nz]
    have m1 : (2 * b + 1) % 2 = 1 := by
      simp [Nat.add_mod]
    simp [m1]
    have h1 : (2 * b + 1) / 2 = b := by
      simp [Nat.add_div]
    simp [h1]
    rw [hyp]


open Lean Meta Elab Tactic

def eqnExpr (a b m n : ℕ) : MetaM Expr := do
    let aExp := toExpr a
    let bExp := toExpr b
    let mExp := toExpr m
    let nExp := toExpr n
    let lhs := mkAppN (mkConst ``powerMod) #[aExp, bExp, mExp]
    mkEq lhs nExp

def simplifyPowMod (a b m : ℕ): MVarId → MetaM (List (MVarId)) :=
  fun mvarId =>
    mvarId.withContext do
    let n := powerMod a b m
    let expectedType ← eqnExpr a b m n
    let goalType ← mvarId.getType
    if !(← isDefEq goalType expectedType) then
      throwError s!"unexpected type: goal is {← ppExpr goalType}; computation gives {← ppExpr expectedType}"
    let rec loop (b : ℕ)(mvarId : MVarId) :  MetaM Unit := do
      if b = 0 then
        let expr ← (mkAppM ``zero_powerMod #[toExpr  a, toExpr  m])
        mvarId.assign expr
      else
        if b % 2 = 0 then
          let b' := b/2
          let n' := powerMod a (b/2) m
          let prevGoal ← eqnExpr a b' m n'
          let mvarId' ← mkFreshMVarId
          let mvar' ← mkFreshExprMVarWithId mvarId' (some prevGoal)
          let expr ← (mkAppM ``even_powerMod
            #[toExpr  a, toExpr  b', toExpr  m,
            toExpr  n', mvar'])
          mvarId.assign expr
          loop (b/2)  mvarId'
        else
          let b' := b/2
          let n' := powerMod a (b/2) m
          let prevGoal ← eqnExpr a b' m n'
          let mvarId' ← mkFreshMVarId
          let mvar' ← mkFreshExprMVarWithId mvarId' (some prevGoal)
          let expr ← (mkAppM ``odd_powerMod
            #[toExpr  a, toExpr  b', toExpr  m,
            toExpr  n', mvar'])
          mvarId.assign expr
          loop (b/2)  mvarId'
    loop b  mvarId
    return []


elab "simplify_power_mod"
    a:num "^" b:num "%" m:num  : tactic =>
    liftMetaTactic <|
      simplifyPowMod a.getNat b.getNat m.getNat

elab "simplify_power_mod#"
    a:num "^" b:num "%" m:num  : term => do
    let n := powerMod a.getNat b.getNat m.getNat
    let goal ← eqnExpr a.getNat b.getNat m.getNat n
    let mvarId ← mkFreshMVarId
    let mvar ← mkFreshExprMVarWithId mvarId (some goal)
    let _ ← simplifyPowMod a.getNat b.getNat m.getNat mvarId
    return mvar

elab "simplify_power_mod#"
    a:num "^" "(" b':num "/" q:num ")" "%" m:num  : term => do
    let b := b'.getNat / q.getNat
    let n := powerMod a.getNat b m.getNat
    let goal ← eqnExpr a.getNat b m.getNat n
    let mvarId ← mkFreshMVarId
    let mvar ← mkFreshExprMVarWithId mvarId (some goal)
    let _ ← simplifyPowMod a.getNat b m.getNat mvarId
    return mvar


#eval powerMod 2232421124 10027676 121 -- 45

example : powerMod 2232421124 10027676 121 = 45 := by
  simplify_power_mod 2232421124 ^ 10027676 % 121

example : powerMod 2232421124 10027676 121 = 45 := by
  have := simplify_power_mod# 2232421124 ^ 10027676 % 121
  rw [this]

example : ¬ powerMod 2232421124 10027676 121 = 41 := by
  have := simplify_power_mod# 2232421124 ^ 10027676 % 121
  rw [this]
  simp
