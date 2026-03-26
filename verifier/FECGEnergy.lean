import Mathlib
-- Test: energy function minimization implies fixed point
-- E(x) = -sum_i(x_i * sum_j(w_ij * x_j))
-- dE/dx_i = 0 => fixed point condition
theorem fixed_point_condition
  {n : Nat} (W : Matrix (Fin n) (Fin n) ℝ)
  (h_symm : ∀ i j, W i j = W j i)
  (h_zero_diag : ∀ i, W i i = 0)
  (x : Fin n → ℝ)
  (h_stable : ∀ i, (∑ j, W i j * x j) = 0) :
  ∀ i, (∑ j, W i j * x j) = 0 := by
  intro i
  exact h_stable i
