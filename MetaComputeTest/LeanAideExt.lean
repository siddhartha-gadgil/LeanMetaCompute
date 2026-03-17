import MetaCompute.Tactic.PrimalityReduce
import LeanAideCore.PaperCodes
import LeanAideCore.Kernel
import LeanAideCore.Responses

open LeanAide Lean Meta Lean.Parser.Tactic

@[codegen "primality_proof"]
def primalityCode (_ : CodeGenerator := {}) :
    Option MVarId →  (kind: SyntaxNodeKinds) → Json → TranslateM (Option (TSyntax kind))
| _, ``tacticSeq, _ => do
  let tacs := #[← `(tactic| repeat primality_reduce)]
  `(tacticSeq| $tacs*)
| goal?, kind ,_ => throwError
    s!"codegen: induction does not work for kind {kind} with goal present: {goal?.isSome}"

example : Nat.Prime 48611 := by repeat primality_reduce

-- #stopLogs

-- #codegen induction_eg
def primality_eg := json% {
  "theorem" : {
    "claim" : "Nat.Prime 85083351022467190124442353598696803287939269665617",
    "proof" : {"primality_proof" : {}}
  }
}

#codegen primality_eg
