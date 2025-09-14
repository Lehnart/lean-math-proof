import Mathlib.Data.Real.Basic

example (a b c : ℝ) : c * b * a = b * (a * c) :=
  calc
    c * b * a = b * a * c := mul_assoc 


example (a b c : ℝ) : a * (b * c) = b * (a * c) := by
  sorry
