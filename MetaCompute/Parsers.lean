import Std.Internal.Parsec.String
/-!
## Pari interface helpers
This file provides parsers for the output of the Pari library.
-/

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

def getFactors (s : String) : IO <| List (Nat × Nat) := do
  IO.ofExcept <| parseFactors.run s |>.mapError ("Error getting factors: " ++ ·)

def parsePrimitiveRootOf (base : Nat) : String.Parser Nat := do
  ws
  skipString "Mod"
  skipChar '('
  ws
  let root ← digits
  ws
  skipChar ','
  ws
  let p ← digits
  unless p == base do
    fail s!"Expected base {base}, but got {p}"
  ws
  skipChar ')'
  ws
  eof
  return root

def getPrimitiveRootOf (base : Nat) (s : String) : IO <| Nat := do
  IO.ofExcept <| (parsePrimitiveRootOf base).run s |>.mapError ("Error getting primitive root: " ++ ·)
