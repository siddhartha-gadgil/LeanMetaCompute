import MetaCompute.Pari
import MetaCompute.PrattCertificate

open Lean Elab Meta Term Tactic
open pari

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
unsafe def Lean.Meta.mkAppAutoM (constName : Name) (args : Array Expr) : TacticM Expr := do
  mkAppN (mkConst constName) args |>.applyAutoParamArgs

elab "primality_reduce" : tactic => unsafe withMainContext do
  let_expr Nat.Prime pE := ← getMainTarget | throwError "target is not of the form `Nat.Prime _`"
  let some p ← getNatValue? (← reduce pE) | throwError "Failed to obtain a natural number from {pE}"
  let check ← queryPari s!"isprime({p})"
  unless check = "1" do
    throwError "{pE} is not a prime (according to Pari)"
  let a ← znPrimRoot p
  logInfo m!"Primitive root: {a}"
  let factors := (← factors (p - 1)) |>.map fun (q, e) ↦ (q, e - 1)
  logInfo m!"Factors: {factors}"
  let cert ← mkAppAutoM ``PrattCertificate.mk #[pE, toExpr a, toExpr factors]
  let primeProof ← mkAppM ``pratt_certification #[pE, cert]
  (← getMainGoal).assignIfDefEq primeProof
  pruneSolvedGoals
