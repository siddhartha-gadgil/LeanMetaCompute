import MetaCompute.Tactic.PrimalityReduce

example : Nat.Prime 48611 := by
  primality_reduce
  · primality_reduce

example : Nat.Prime 85083351022467190124442353598696803287939269665617 := by repeat primality_reduce
