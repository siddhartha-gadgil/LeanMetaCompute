import MetaCompute.Tactic.Pratt

example : Nat.Prime 19 := by
  pratt_step 2 [ (2 ^ 1), (3 ^ 2) ]
  · decide
  · decide

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


/-
Proving a large prime number using the `pratt` tactic. A code action allows you to generate the proof script for the `pratt` tactic, so that calls to pari-gp are not required for the generated script.
-/
example : Nat.Prime 85083351022467190124442353598696803287939269665617 := by
  pratt
