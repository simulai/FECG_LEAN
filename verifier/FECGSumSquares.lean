import Mathlib
-- FECG energy: sum of squared elements
theorem sum_squares_pos
  {n : Nat} (x : Fin n → ℝ) :
  0 ≤ ∑ i, (x i)^2 := by
  simp only
  positivity
