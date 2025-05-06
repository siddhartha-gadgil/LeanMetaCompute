import MetaCompute.PowerMod

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
