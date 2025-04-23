import Std.Internal.Parsec.String

open Lean Std Internal Parsec String

partial def parseFactors : String.Parser (List (Nat × Nat)) := do
  if ← isEof then
    return []
  ws
  skipChar '['
  ws
  let p ← digits
  ws
  let e ← digits
  ws
  skipChar ']'
  ws
  let tail ← parseFactors
  return (p, e) :: tail

def testOutput := "
[     2 2]

[ 35227 1]

[609809 1]

"

#eval parseFactors|>.run testOutput
