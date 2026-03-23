import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Topology.Instances.ENNReal
import Mathlib.Data.Finset.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Instances.Real
import Mathlib.Analysis.NormedSpace.Basic
import Mathlib.Logic.Function.Iterate
import Mathlib.Analysis.SpecificLimits.Basic

open Filter Topology BigOperators

-- Define the dimension of the state space for each node
variable {N d : ℕ}

-- 1. System Definition
-- Node state space (d-dimensional Euclidean space)
-- We use EuclideanSpace which is a PiL2 type equipped with inner product and norm.
abbrev State (d : ℕ) := EuclideanSpace ℝ (Fin d)

-- Global state: A collection of N node states
-- We model this as a function from node index to node state.
abbrev CompositeState (N d : ℕ) := Fin N → State d

-- Internal energy of node i: E_i(x_i)
variable (E_i : Fin N → State d → ℝ)

-- Coupling energy between node i and j: C_ij(x_i, x_j)
variable (C_ij : Fin N → Fin N → State d → State d → ℝ)

-- Total Energy Function
-- E_total X = ∑ E_i(x_i) + ∑∑ C_ij(x_i, x_j)
noncomputable def E_total (X : CompositeState N d) : ℝ :=
  (∑ i : Fin N, E_i i (X i)) + (∑ i : Fin N, ∑ j : Fin N, C_ij i j (X i) (X j))

-- 2. Dynamics
-- Discrete time update rule F
variable (F : CompositeState N d → CompositeState N d)

-- Assumptions on the system
section Assumptions

-- a) F is continuous
variable (h_cont_F : Continuous F)

-- b) Energy is non-increasing along the trajectory
variable (h_E_decreasing : ∀ X, E_total E_i C_ij (F X) ≤ E_total E_i C_ij X)

-- c) Energy is bounded below (stability requirement)
variable (h_E_bounded : ∃ B, ∀ X, E_total E_i C_ij X ≥ B)

-- d) Strict energy decrease for non-fixed points (Lyapunov condition)
variable (h_E_strict : ∀ X, F X ≠ X → E_total E_i C_ij (F X) < E_total E_i C_ij X)

-- e) E_total is continuous (usually implied by continuity of E_i and C_ij)
variable (h_cont_E : Continuous (E_total E_i C_ij))

end Assumptions

-- 3. Theorems

/--
Theorem 1: Energy Sequence Convergence
For any initial state X0, the sequence of total energies E(F^k(X0)) converges.
This relies on the Monotone Convergence Theorem (for sequences bounded below).
-/
theorem composite_energy_converges (X0 : CompositeState N d) :
  Tendsto (fun k => E_total E_i C_ij (F^[k] X0)) atTop (𝓝 (⨅ k, E_total E_i C_ij (F^[k] X0))) := by
  -- 1. The sequence is monotonically decreasing
  have h_mono : Antitone (fun k => E_total E_i C_ij (F^[k] X0)) := by
    apply antitone_nat_of_succ_le
    intro k
    -- E(x_{k+1}) <= E(x_k) by h_E_decreasing
    simp only [Function.iterate_succ']
    apply h_E_decreasing

  -- 2. The sequence is bounded below
  have h_bdd : BddBelow (Set.range (fun k => E_total E_i C_ij (F^[k] X0))) := by
    rcases h_E_bounded with ⟨B, hB⟩
    use B
    intro y hy
    rcases hy with ⟨k, rfl⟩
    exact hB (F^[k] X0)

  -- 3. Apply Monotone Convergence Theorem (tendsto_atTop_ciInf)
  exact tendsto_atTop_ciInf h_mono h_bdd

/--
Theorem 2: Limit Point is Fixed Point
If the trajectory converges to a state X*, then X* must be a fixed point of F.
This uses a Lasalle Invariance Principle type argument.
-/
theorem composite_limit_is_fixed_point 
    (X0 : CompositeState N d) (X_star : CompositeState N d) 
    (h_lim : Tendsto (fun k => F^[k] X0) atTop (𝓝 X_star)) : 
    F X_star = X_star := by
  
  -- 1. Energy sequence E(x_k) converges to E(X*) by continuity of E
  have h_E_lim : Tendsto (fun k => E_total E_i C_ij (F^[k] X0)) atTop (𝓝 (E_total E_i C_ij X_star)) :=
    h_cont_E.tendsto.comp h_lim

  -- 2. Consider the shifted sequence x_{k+1} = F(x_k).
  -- Since x_k -> X*, x_{k+1} also -> X*.
  have h_lim_shift : Tendsto (fun k => F^[k+1] X0) atTop (𝓝 X_star) :=
    h_lim.comp (Filter.tendsto_add_atTop_nat 1)

  -- 3. By continuity of F, F(x_k) -> F(X*).
  -- Note that F(x_k) is exactly x_{k+1}.
  have h_lim_F : Tendsto (fun k => F (F^[k] X0)) atTop (𝓝 (F X_star)) :=
    h_cont_F.tendsto.comp h_lim
  
  -- 4. So we have x_{k+1} -> X* AND x_{k+1} -> F(X*).
  -- By uniqueness of limits in a Hausdorff space (EuclideanSpace is T2), F(X*) = X*.
  -- However, we can also prove it via energy contradiction to use the Lyapunov function properties explicitly.
  
  -- Let's use the energy argument as requested in the prompt:
  -- "F X_star ≠ X_star implies E(F X_star) < E(X_star)"
  
  -- Energy of shifted sequence E(x_{k+1}) converges to E(F X*)
  have h_E_lim_F : Tendsto (fun k => E_total E_i C_ij (F^[k+1] X0)) atTop (𝓝 (E_total E_i C_ij (F X_star))) :=
    h_cont_E.tendsto.comp h_lim_F

  -- Energy of shifted sequence E(x_{k+1}) is a subsequence of E(x_k), so it converges to E(X*)
  have h_E_lim_shift : Tendsto (fun k => E_total E_i C_ij (F^[k+1] X0)) atTop (𝓝 (E_total E_i C_ij X_star)) :=
    h_E_lim.comp (Filter.tendsto_add_atTop_nat 1)

  -- By uniqueness of limits, E(F X*) = E(X*)
  have h_E_eq : E_total E_i C_ij (F X_star) = E_total E_i C_ij X_star :=
    tendsto_nhds_unique h_E_lim_F h_E_lim_shift

  -- 5. Contradiction
  -- If F X* != X*, then E(F X*) < E(X*) by h_E_strict.
  -- But we just proved E(F X*) = E(X*).
  by_contra h_neq
  have h_lt := h_E_strict X_star h_neq
  exact ne_of_lt h_lt h_E_eq

/--
Theorem 3: Equilibrium Condition
This theorem asserts that if X_star is a fixed point, it is a stationary point of the energy function.
We assume the dynamics F are compatible with the energy landscape in the sense that
fixed points of F correspond to critical points of E (e.g., F is a gradient descent step).
-/
theorem composite_equilibrium_condition 
    (X_star : CompositeState N d) (h_fixed : F X_star = X_star) 
    -- Assumption: F drives the system to critical points (gradient compatibility)
    -- This is a property of the specific update rule F used in the implementation.
    (h_gradient_dynamics : ∀ X, F X = X ↔ fderiv ℝ (E_total E_i C_ij) X = 0) : 
    fderiv ℝ (E_total E_i C_ij) X_star = 0 := by
    -- The proof is immediate from the gradient dynamics assumption.
    rw [← h_gradient_dynamics]
    exact h_fixed

section Async

variable (F_i : Fin N → CompositeState N d → State d)

def async_iterate (s : ℕ → Fin N) (X0 : CompositeState N d) : ℕ → CompositeState N d
| 0 => X0
| k + 1 =>
  let Xk := async_iterate s X0 k
  let i := s k
  Function.update Xk i (F_i i Xk)

theorem async_energy_converges (s : ℕ → Fin N) (X0 : CompositeState N d)
    (h_local_decreasing : ∀ i X,
      let X' := Function.update X i (F_i i X)
      E_total E_i C_ij X' ≤ E_total E_i C_ij X)
    (h_E_bounded_async : ∃ B, ∀ X, E_total E_i C_ij X ≥ B) :
    Tendsto (fun k => E_total E_i C_ij (async_iterate F_i s X0 k)) atTop
      (𝓝 (⨅ k, E_total E_i C_ij (async_iterate F_i s X0 k))) := by
  have h_mono : Antitone (fun k => E_total E_i C_ij (async_iterate F_i s X0 k)) := by
    apply antitone_nat_of_succ_le
    intro k
    have h := h_local_decreasing (s k) (async_iterate F_i s X0 k)
    simpa [async_iterate] using h
  have h_bdd : BddBelow (Set.range (fun k => E_total E_i C_ij (async_iterate F_i s X0 k))) := by
    rcases h_E_bounded_async with ⟨B, hB⟩
    use B
    intro y hy
    rcases hy with ⟨k, rfl⟩
    exact hB _
  exact tendsto_atTop_ciInf h_mono h_bdd

theorem async_limit_is_fixed (s : ℕ → Fin N) (X0 : CompositeState N d) (X_star : CompositeState N d)
    (h_lim : Tendsto (async_iterate F_i s X0) atTop (𝓝 X_star))
    (h_fair : ∀ i, ∃ φ, StrictMono φ ∧ Tendsto φ atTop atTop ∧ ∀ n, s (φ n) = i)
    (h_cont_F_i : ∀ i, Continuous (F_i i))
    (h_strict : ∀ i X, X i ≠ F_i i X →
      E_total E_i C_ij (Function.update X i (F_i i X)) < E_total E_i C_ij X) :
    ∀ i, F_i i X_star = X_star i := by
  classical
  intro i
  obtain ⟨φ, h_mono_φ, h_lim_φ, h_s_φ⟩ := h_fair i
  have h_lim_sub : Tendsto (fun n => async_iterate F_i s X0 (φ n)) atTop (𝓝 X_star) :=
    h_lim.comp h_lim_φ
  have h_lim_shift : Tendsto (fun n => async_iterate F_i s X0 (φ n + 1)) atTop (𝓝 X_star) := by
    have h_tendsto_add : Tendsto (fun n => φ n + 1) atTop atTop :=
      (Filter.tendsto_add_atTop_nat 1).comp h_lim_φ
    exact h_lim.comp h_tendsto_add
  have h_eq : (fun n => async_iterate F_i s X0 (φ n + 1)) =
      (fun n => Function.update (async_iterate F_i s X0 (φ n)) i (F_i i (async_iterate F_i s X0 (φ n)))) := by
    funext n
    simp [async_iterate, h_s_φ n]
  have h_cont_update : Continuous (fun X => Function.update X i (F_i i X)) := by
    apply Continuous.update
    · exact continuous_id
    · exact h_cont_F_i i
  have h_lim_update :
      Tendsto (fun n => Function.update (async_iterate F_i s X0 (φ n)) i (F_i i (async_iterate F_i s X0 (φ n))))
        atTop (𝓝 (Function.update X_star i (F_i i X_star))) :=
    h_cont_update.tendsto.comp h_lim_sub
  have h_lim_shift' :
      Tendsto (fun n => Function.update (async_iterate F_i s X0 (φ n)) i (F_i i (async_iterate F_i s X0 (φ n))))
        atTop (𝓝 X_star) := by
    simpa [h_eq] using h_lim_shift
  have h_eq_star : Function.update X_star i (F_i i X_star) = X_star :=
    tendsto_nhds_unique h_lim_update h_lim_shift'
  have h_at_i : F_i i X_star = X_star i := by
    have := congrArg (fun X => X i) h_eq_star
    simpa using this
  exact h_at_i

end Async

-- 5. Robustness under Bounded Perturbations
section Robustness

variable (e : ℕ → CompositeState N d) -- Perturbation sequence (e.g., communication noise)

/--
Perturbed Asynchronous Update:
At each step, we update node i with F_i, BUT add a perturbation e_k.
X_{k+1} = update(X_k, i, F_i(X_k)) + e_k
-/
def perturbed_async_iterate (s : ℕ → Fin N) (X0 : CompositeState N d) : ℕ → CompositeState N d
| 0 => X0
| (k+1) => 
    let i := s k
    let Xk := perturbed_async_iterate s X0 k
    let X_ideal := Function.update Xk i (F_i i Xk)
    X_ideal + e k

-- Assumption: E is Lipschitz continuous (or uniformly continuous)
-- Here we assume global Lipschitz continuity with constant K
variable (K : ℝ) (h_K_pos : K ≥ 0)
variable (h_lipschitz_E : LipschitzWith (NNReal.ofReal K) (E_total E_i C_ij))

-- Assumption: Perturbations are summable (total noise is finite)
-- This models transient errors or decaying noise in the system
variable (h_summable_e : Summable (fun k => ‖e k‖))

/--
Lemma: Quasi-Decreasing Convergence
If a sequence u_n satisfies u_{n+1} ≤ u_n + ε_n where ∑ ε_n < ∞,
and u_n is bounded below, then u_n converges.
-/
lemma tendsto_of_quasi_decreasing (u : ℕ → ℝ) (ε : ℕ → ℝ) 
  (h_bound : BddBelow (Set.range u))
  (h_quasi : ∀ n, u (n+1) ≤ u n + ε n)
  (h_ε_nonneg : ∀ n, 0 ≤ ε n)
  (h_sum : Summable ε) :
  ∃ l, Tendsto u atTop (𝓝 l) := by
  -- Construct a modified sequence v_n = u_n - ∑_{k=0}^{n-1} ε_k
  -- Then v_{n+1} - v_n = u_{n+1} - u_n - ε_n ≤ 0, so v_n is decreasing.
  -- Since u_n is bounded below and ∑ ε_k converges, v_n is bounded below.
  -- Thus v_n converges, implying u_n converges.
  let S := fun n => ∑ k in Finset.range n, ε k
  let v := fun n => u n - S n
  have h_dec : Antitone v := by
    apply antitone_nat_of_succ_le
    intro n
    dsimp [v, S]
    rw [Finset.sum_range_succ]
    linarith [h_quasi n]
  
  have h_bdd_v : BddBelow (Set.range v) := by
    rcases h_bound with ⟨B, hB⟩
    -- S n is bounded above by total sum
    have h_sum_bdd : BddAbove (Set.range S) := 
      summable_of_nonneg_of_le (fun n => h_ε_nonneg n) (fun n => le_refl _) h_sum |> Summable.hasSum |> HasSum.bddAbove_range_of_nonneg h_ε_nonneg
    rcases h_sum_bdd with ⟨M, hM⟩
    use B - M
    intro y hy
    rcases hy with ⟨n, rfl⟩
    specialize hB n
    specialize hM n
    dsimp [v]
    linarith
  
  have h_lim_v : ∃ l_v, Tendsto v atTop (𝓝 l_v) := tendsto_atTop_ciInf h_dec h_bdd_v |> Exists.intro _
  rcases h_lim_v with ⟨l_v, h_tendsto_v⟩
  
  have h_lim_S : Tendsto S atTop (𝓝 (∑' n, ε n)) := h_sum.hasSum.tendsto_sum_nat
  
  -- u_n = v_n + S n -> l_v + sum
  exists l_v + (∑' n, ε n)
  have h_u_eq : u = fun n => v n + S n := by ext n; simp [v]
  rw [h_u_eq]
  exact h_tendsto_v.add h_lim_S

/--
Theorem 3: Robust Convergence under Summable Perturbations
If the system is subject to summable perturbations (e.g., decaying noise or finite packet errors),
and the energy function is Lipschitz, the energy sequence still converges.
-/
theorem robust_async_energy_converges (s : ℕ → Fin N) (X0 : CompositeState N d) :
  ∃ l, Tendsto (fun k => E_total E_i C_ij (perturbed_async_iterate e s X0 k)) atTop (𝓝 l) := by
  let u := fun k => E_total E_i C_ij (perturbed_async_iterate e s X0 k)
  let ε := fun k => K * ‖e k‖
  
  -- 1. Verify u_{k+1} <= u_k + ε_k
  have h_quasi : ∀ k, u (k+1) ≤ u k + ε k := by
    intro k
    dsimp [u, perturbed_async_iterate]
    let Xk := perturbed_async_iterate e s X0 k
    let i := s k
    let X_ideal := Function.update Xk i (F_i i Xk)
    let X_next := X_ideal + e k
    
    -- E(X_next) <= E(X_ideal) + K * ||X_next - X_ideal||
    have h_lip : dist (E_total E_i C_ij X_next) (E_total E_i C_ij X_ideal) ≤ K * dist X_next X_ideal := by
      -- LipschitzWith K f -> dist (f x) (f y) <= K * dist x y
      have := h_lipschitz_E.dist_le_mul X_next X_ideal
      rw [NNReal.coe_ofReal] at this
      exact this
      exact h_K_pos
      
    -- dist X_next X_ideal = ||e k||
    have h_dist : dist X_next X_ideal = ‖e k‖ := by
      rw [dist_eq_norm]
      have : X_next - X_ideal = e k := by abel
      rw [this]
    
    -- E(X_ideal) <= E(Xk) by local decreasing property
    have h_local := h_local_decreasing i Xk
    
    -- Combine: E(X_next) <= E(X_ideal) + K*||e k|| <= E(Xk) + K*||e k||
    -- Note: dist (E a) (E b) = |E a - E b|
    rw [Real.dist_eq, abs_sub_le_iff] at h_lip
    have h_E_le : E_total E_i C_ij X_next - E_total E_i C_ij X_ideal ≤ K * ‖e k‖ := by
      rw [h_dist] at h_lip
      exact h_lip.1
      
    linarith [h_local, h_E_le]

  -- 2. Verify ε is summable
  have h_sum_ε : Summable ε := by
    apply Summable.mul_left
    exact h_summable_e

  -- 3. Verify u is bounded below (assuming perturbations don't drive it to -infinity)
  -- Wait, with perturbations, energy could drop indefinitely if not careful?
  -- But we assume E is bounded below globally (h_E_bounded).
  have h_bdd : BddBelow (Set.range u) := by
    rcases h_E_bounded with ⟨B, hB⟩
    use B
    intro y hy
    rcases hy with ⟨k, rfl⟩
    exact hB _

  -- 4. Apply lemma
  apply tendsto_of_quasi_decreasing u ε h_bdd h_quasi (fun k => mul_nonneg h_K_pos (norm_nonneg _)) h_sum_ε

end Robustness
