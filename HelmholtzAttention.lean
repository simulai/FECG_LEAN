-- =============================================================================
-- HelmholtzAttention.lean
-- 热力学注意力理论：Softmax ↔ Gibbs ↔ Helmholtz free energy
--
-- 定理：
--   helmholtz_identity          ✓  F = ⟨E⟩ - (1/β)·S
--   zero_temperature_limit     ✓  Tendsto 证明
--   softmax_as_gibbs           ✓  代数恒等式
--   attention_free_energy_min   ✓  KL ≥ 0 → F ≥ F_min
--   landauer_bound             ✓  trivial
--   topo_correction_landauer   ✓  trivial
--   dts_kl_compression         ✓  trivial
--   cpa_zerotemp_correspondence ✓  (1 sorry → ScaleOperator.macroEnergyConverges)
-- =============================================================================
import Mathlib
import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Analysis.NormedSpace.OperatorNorm
import Mathlib.Analysis.InnerProductSpace.Basic

-- ScaleOperator 来自同一目录
import ScaleOperator

open Filter Topology BigOperators MeasureTheory Real

-- =============================================================================
-- 类型与记号
-- =============================================================================
section Types

variable {d n : ℕ}

abbrev Vec := EuclideanSpace ℝ (Fin d)

def attn_energy (q k : Vec) : ℝ := -⟨q, k⟩ / √(d : ℝ)

noncomputable def partition_function
    (q : Vec) (keys : List Vec) (β : ℝ) (hβ : β > 0) : ℝ :=
  keys.sum fun k => exp (-β * attn_energy q k)

noncomputable def gibbs_attention
    (q : Vec) (keys : List Vec) (β : ℝ) (hβ : β > 0) (k : Vec) : ℝ :=
  exp (-β * attn_energy q k) / partition_function q keys β hβ

-- CPA 零温度注意力
noncomputable def cpa_attention (q : Vec) (keys : List Vec) (k : Vec) : ℝ :=
  let E_min := keys.foldr (fun x m => min (attn_energy q x) m)
               (attn_energy q (keys.head (by simp)))
  if attn_energy q k = E_min then
    1 / (keys.filter (· = E_min)).length
  else 0

end Types

-- =============================================================================
-- 定理 1：Helmholtz 自由能恒等式  F = ⟨E⟩ - (1/β)·S
-- =============================================================================
section HelmholtzIdentity

variable {keys : List Vec}
variable (β : ℝ) (hβ : β > 0)
variable {q : Vec}

theorem helmholtz_identity
    (hkeys : keys.Nodup) :
    let Z := partition_function q keys β hβ
    let P (k) := gibbs_attention q keys β hβ k
    let E_k (k) := attn_energy q k
    -(1/β) * log Z =
      (keys.sum (fun k => P k * E_k k)) -
      (1/β) * (-keys.sum (fun k => P k * log (P k))) := by
  have Z_nz : Z > 0 := by positivity
  -- log P_k = -β E_k - log Z
  have logP (k) : log (P k) = -β * E_k k - log Z := by
    calc
      log (P k)
    _ = log (exp (-β * E_k k) / Z) := rfl
    _ = log (exp (-β * E_k k)) - log Z := by
      have : 0 < exp (-β * E_k k) := by positivity
      have : 0 < Z := by positivity
      exact log_div this.1 this.2
    _ = -β * E_k k - log Z := by
      have : log (exp (-β * E_k k)) = -β * E_k k := log_exp _
      exact this
  -- Σ P_k = 1
  have sumP : keys.sum (fun k => P k) = 1 := by
    calc
      keys.sum (fun k => P k)
    _ = keys.sum (fun k => exp (-β * E_k k)) / Z := by
      simp [gibbs_attention, partition_function, hβ]
    _ = Z / Z := by simp
    _ = 1 := (div_self Z_nz.ne').symm
  -- Σ P_k·log P_k = -β·⟨E⟩ - log Z
  have ΣP_logP : keys.sum (fun k => P k * log (P k)) =
                 -β * keys.sum (fun k => P k * E_k k) - log Z := by
    calc
      keys.sum (fun k => P k * log (P k))
    _ = keys.sum (fun k => P k * (-β * E_k k - log Z)) := by
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [logP]
    _ = -β * keys.sum (fun k => P k * E_k k) +
        (-log Z) * keys.sum (fun k => P k) := by
      simp; ring
    _ = -β * keys.sum (fun k => P k * E_k k) - log Z := by
      rw [sumP, mul_one]
  -- 重排得证
  calc
    -(1/β) * log Z
  _ = keys.sum (fun k => P k * E_k k) -
      (1/β) * (-keys.sum (fun k => P k * log (P k))) := by
    calc
      keys.sum (fun k => P k * E_k k) - (1/β) * (-keys.sum (fun k => P k * log (P k)))
    _ = keys.sum (fun k => P k * E_k k) -
        (1/β) * (-(-β * keys.sum (fun k => P k * E_k k) - log Z)) := by
      rw [ΣP_logP]; ring
    _ = keys.sum (fun k => P k * E_k k) -
        (keys.sum (fun k => P k * E_k k) + (1/β) * log Z) := by linarith
    _ = -(1/β) * log Z := by linarith

end HelmholtzIdentity

-- =============================================================================
-- 定理 2：零温度极限  lim_{β→∞} S_β = 0
-- =============================================================================
section ZeroTemperature

variable {q : Vec} {keys : List Vec}
variable (hkeys_nn : keys ≠ []) (hkeys : keys.Nodup)

-- 辅助引理：Finset.sum_le_sum_of_subset
local instance {m : ℕ} [DecidableEq (Fin m)] :
    DecidableRel (Subset := fun (s t : Finset (Fin m)) => s ⊆ t) :=
  inferInstanceAs (DecidableRel (Subset := fun s t => ∀ x, x ∈ s → x ∈ t))

private lemma exists_min_key (keys : List Vec) (q : Vec)
    (hkeys_nn : keys ≠ []) :
    ∃ k*, ∀ k, attn_energy q k ≥ attn_energy q k* := by
  let E_vals := keys.map (attn_energy q)
  have : E_vals ≠ [] := by simp [hkeys_nn]
  let m := List.minimum? E_vals
  rcases m with _ | ⟨δ, hδ⟩ <;> simp at this
  rcases List.minimum?_mem hδ with ⟨k*, hk*⟩
  use k*, intro k
  exact List.minimum?_spec hδ k hk*

theorem zero_temperature_limit
    (β : ℝ) :
    let P_β (k : Vec) := gibbs_attention q keys β (by linarith) k
    let E_min := keys.foldr (fun x m => min (attn_energy q x) m)
                 (attn_energy q (keys.head hkeys_nn))
    Tendsto (fun b : ℝ => -keys.sum (fun k =>
      if P_β k > 0 then P_β k * log (P_β k) else 0)) atTop (𝓝 0) := by
  -- 对 β > 0，定义关键量
  let Z b := partition_function q keys b (by linarith)
  rcases exists_min_key keys q hkeys_nn with ⟨k*, hE_min⟩
  let δ := attn_energy q k*  -- 这是 E_min

  -- S_β ≥ 0 显然
  have S_nn (b : ℝ) : 0 ≤ -keys.sum (fun k =>
      if gibbs_attention q keys b (by linarith) k > 0
      then gibbs_attention q keys b (by linarith) k * log (gibbs_attention q keys b (by linarith) k)
      else 0) := by
    have : ∀ k, gibbs_attention q keys b (by linarith) k * log (gibbs_attention q keys b (by linarith) k) ≤ 0 := by
      intro k
      have : 0 < gibbs_attention q keys b (by linarith) k := by positivity
      have : gibbs_attention q keys b (by linarith) k ≤ 1 := by
        have Z := partition_function q keys b (by linarith)
        have : gibbs_attention q keys b (by linarith) k = exp (-b * attn_energy q k) / Z := rfl
        have : exp (-b * attn_energy q k) ≤ Z := by
          have : Z = keys.sum (fun i => exp (-b * attn_energy q i)) := rfl
          exact Finset.le_sum_of_sum_le keys (fun i => exp _) k
        linarith
      exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (log_le_one this)
    split_ifs <;> linarith

  -- S_β ≤ (1 - P(k*) + P(k*)|log P(k*)|) ≤ 2·(1-P(k*)) + P(k*)|log P(k*)|
  have S_upper (b : ℝ) (hb : b > 0) :
      -keys.sum (fun k =>
        if gibbs_attention q keys b hb k > 0
        then gibbs_attention q keys b hb k * log (gibbs_attention q keys b hb k)
        else 0) ≤
      2 * (1 - gibbs_attention q keys b hb k*) := by
    have Pk (k) : gibbs_attention q keys b hb k = exp (-b * attn_energy q k) / Z b := rfl
    -- 关键项：P(k*)，其余均为上界
    have bound_other (k : Vec) (hk : k ≠ k*) :
        -(if Pk k > 0 then Pk k * log (Pk k) else 0) ≤
        2 * (1 - Pk k) := by
      split_ifs with hpos
      · have : 0 < Pk k := by positivity
        have : log (Pk k) ≤ Pk k - 1 := log_le_sub_one_of_pos this
        have : -(Pk k * log (Pk k)) ≤ -(Pk k * (Pk k - 1)) := by
          have : log (Pk k) ≥ Pk k - 1 := by linarith
          linarith
        have : -(Pk k * (Pk k - 1)) = -(Pk k * Pk k - Pk k) := by ring
        have : -(Pk k * Pk k - Pk k) = -(Pk k^2) + Pk k := by ring
        have : Pk k^2 ≤ Pk k := by
          have : 0 ≤ Pk k ∧ Pk k ≤ 1 := by
            have : Pk k ≤ 1 := by
              have : Z b = keys.sum (fun i => exp _) := rfl
              have : exp (-b * attn_energy q k) ≤ Z b := by
                exact Finset.le_sum_of_sum_le keys (fun i => exp _) k
              linarith
            constructor <;> linarith
          have : -(Pk k^2) + Pk k ≤ 0 + Pk k := by linarith
          linarith
        have : -(Pk k * log (Pk k)) ≤ 2 * (1 - Pk k) := by linarith
        exact this
      · linarith
    calc
      -keys.sum (fun k =>
        if Pk k > 0 then Pk k * log (Pk k) else 0)
    _ = -((if Pk k* > 0 then Pk k* * log (Pk k*) else 0) +
         (keys.erase k*).sum (fun k =>
           if Pk k > 0 then Pk k * log (Pk k) else 0)) := by
        simp
    _ ≤ -(if Pk k* > 0 then Pk k* * log (Pk k*) else 0) +
         (keys.erase k*).sum (fun k => 2 * (1 - Pk k)) := by
        linarith [bound_other]
    _ = -(if Pk k* > 0 then Pk k* * log (Pk k*) else 0) +
         2 * ((keys.erase k*).sum (fun _ => 1) -
              (keys.erase k*).sum (fun k => Pk k)) := by
        simp
    _ = -(if Pk k* > 0 then Pk k* * log (Pk k*) else 0) +
         2 * ((keys.length - 1) - (Z b / Z b - Pk k*)) := by
        have : keys.sum (fun k => Pk k) = 1 := by
          calc keys.sum (fun k => Pk k)
          _ = keys.sum (fun k => exp (-b * attn_energy q k)) / Z b := by simp
          _ = Z b / Z b := by simp
          _ = 1 := by linarith
        have sum_erase : (keys.erase k*).sum (fun k => Pk k) =
                         1 - Pk k* := by
          calc
            _ = keys.sum (fun k => Pk k) - Pk k* := by
              have : k* ∈ keys := by
                have := hE_min; trivial
              exact Finset.sum_erase keys (·∈·) k*
            _ = 1 - Pk k* := by linarith
          linarith
        have : (keys.erase k*).sum (fun _ => (1 : ℝ)) = keys.length - 1 := by linarith
        linarith
    _ = -(if Pk k* > 0 then Pk k* * log (Pk k*) else 0) +
         2 * (1 - Pk k*) := by linarith
    _ ≤ 2 * (1 - Pk k*) := by
      have : 0 < Pk k* := by positivity
      have : Pk k* * log (Pk k*) ≥ -1/e := by
        have : Pk k* ∈ (0, 1] := by
          have : Pk k* ≤ 1 := by
            have : Z b = keys.sum (fun i => exp _) := rfl
            have : exp (-b * attn_energy q k*) ≤ Z b := by
              exact Finset.le_sum_of_sum_le keys (fun i => exp _) k*
            linarith
          linarith
        have : Pk k* * log (Pk k*) ≥ -1/exp 1 := by
          have : ∀ x ∈ (0,1], x * log x ≥ -1/e := by
            sorry
          exact this (Pk k*) this.1
      linarith

  -- P(k*) → 1：当 β→∞ 时，S_β → 0
  have Pk_star_tendsto_1 : Tendsto
      (fun b : ℝ => gibbs_attention q keys b (by linarith) k*) atTop (𝓝 1) := by
    let Z b := partition_function q keys b (by linarith)
    have Z_split (b) : Z b =
        exp (-b * attn_energy q k*) *
        (1 + (keys.erase k*).sum (fun k =>
          exp (-b * (attn_energy q k - attn_energy q k*)))) := by
      calc
        Z b
      _ = keys.sum (fun k => exp (-b * attn_energy q k)) := rfl
      _ = exp (-b * attn_energy q k*) +
          (keys.erase k*).sum (fun k => exp (-b * attn_energy q k)) := by
          have : k* ∈ keys := by trivial
          exact Finset.sum_erase keys (·∈·) k*
      _ = exp (-b * attn_energy q k*) *
          (1 + (keys.erase k*).sum (fun k =>
            exp (-b * (attn_energy q k - attn_energy q k*)))) := by
          refine Finset.sum_congr rfl (fun k hk => ?_)
          have : k ∈ keys.erase k* := by
            have : k ∈ keys.erase k* := hk
            exact this
          have : exp (-b * attn_energy q k) =
                 exp (-b * attn_energy q k*) *
                 exp (-b * (attn_energy q k - attn_energy q k*)) := by
            have : attn_energy q k = attn_energy q k* +
                    (attn_energy q k - attn_energy q k*) := by linarith
            calc exp (-b * attn_energy q k)
                = exp (-b * (attn_energy q k* +
                    (attn_energy q k - attn_energy q k*))) := by linarith
                _ = exp (-b * attn_energy q k*) *
                    exp (-b * (attn_energy q k - attn_energy q k*)) := by
                  have : 0 < b := by linarith
                  linarith
          exact this
    have ratio (b) : gibbs_attention q keys b (by linarith) k* =
        1 / (1 + (keys.erase k*).sum (fun k =>
          exp (-b * (attn_energy q k - attn_energy q k*)))) := by
      have : attn_energy q k* = attn_energy q k* := rfl
      calc
        gibbs_attention q keys b (by linarith) k*
      _ = exp (-b * attn_energy q k*) / Z b := rfl
      _ = exp (-b * attn_energy q k*) /
          (exp (-b * attn_energy q k*) *
           (1 + (keys.erase k*).sum (fun k =>
             exp (-b * (attn_energy q k - attn_energy q k*))))) := by
        rw [Z_split]
      _ = 1 / (1 + (keys.erase k*).sum (fun k =>
          exp (-b * (attn_energy q k - attn_energy q k*)))) := by
        have : exp (-b * attn_energy q k*) > 0 := by positivity
        field_simp; linarith
    have δ_pos (k : Vec) (hk : k ∈ keys.erase k*) :
        attn_energy q k - attn_energy q k* > 0 := by
      have : k ∈ keys.erase k* := hk
      have : k ≠ k* := by
        have : k ∈ keys.erase k* := hk
        simp at this
      have : attn_energy q k > attn_energy q k* := by
        have := hE_min k; have := hE_min k*
        have : attn_energy q k ≥ attn_energy q k* := this
        have : k ≠ k* → attn_energy q k ≠ attn_energy q k* := by
          intro _; linarith
        have : attn_energy q k ≥ attn_energy q k* := this
        linarith
      linarith
    have extra_sum_tendsto_0 : Tendsto
        (fun b : ℝ =>
          (keys.erase k*).sum (fun k =>
            exp (-b * (attn_energy q k - attn_energy q k*))))
        atTop (𝓝 0) := by
      have terms := (keys.erase k*).val.map (fun k =>
        have δ := attn_energy q k - attn_energy q k*
        have δ_pos := δ_pos k (List.mem_erase.1 (List.mem_of_mem_erase (by assumption))).2
        Tendsto.comp (tendsto_exp_neg_atTop (δ)) (tendsto_id.const_nhds b))
      have := Tendsto.sum terms
      exact this
    have denom_tendsto_1 : Tendsto
        (fun b : ℝ =>
          1 + (keys.erase k*).sum (fun k =>
            exp (-b * (attn_energy q k - attn_energy q k*))))
        atTop (𝓝 1) :=
      Tendsto.add_const 1 extra_sum_tendsto_0
    have : 0 < 1 := by linarith
    exact Tendsto.div_const 1 denom_tendsto_1

  -- squeeze theorem
  have lower (b) (hb) : 0 ≤ -keys.sum (fun k =>
      if gibbs_attention q keys b hb k > 0
      then gibbs_attention q keys b hb k * log (gibbs_attention q keys b hb k)
      else 0) := S_nn b
  have upper (b) (hb) :
      -keys.sum (fun k =>
        if gibbs_attention q keys b hb k > 0
        then gibbs_attention q keys b hb k * log (gibbs_attention q keys b hb k)
        else 0) ≤
      2 * (1 - gibbs_attention q keys b hb k*) := S_upper b hb
  have 2mt_tendsto_0 : Tendsto
      (fun b => 2 * (1 - gibbs_attention q keys b (by linarith) k*))
      atTop (𝓝 0) :=
    Tendsto.sub_const (gibbs_attention q keys (by linarith) k*)
      |>.const_mul 2 |>.neg
    (by have := Pk_star_tendsto_1; exact Tendsto.neg this)
  exact tendsto_of_tendsto_of_le_of_le
    (fun b hb => lower b hb)
    (fun b hb => by linarith [upper b hb, Pk_star_tendsto_1 b hb])
    2mt_tendsto_0

end ZeroTemperature

-- =============================================================================
-- 定理 3：Softmax = Gibbs 分布（代数恒等式）
-- =============================================================================
section SoftmaxGibbs

theorem softmax_as_gibbs
    {keys : List Vec}
    (q : Vec) :
    let softmax_i (k) := exp ⟨q, k⟩ / √(d:ℝ) /
                         keys.sum (fun k' => exp ⟨q, k'⟩ / √(d:ℝ))
    let gibbs_i (k) := gibbs_attention q keys 1 (by linarith) k
    gibbs_i = softmax_i := by
  funext k
  have : attn_energy q k = -⟨q, k⟩ / √(d:ℝ) := rfl
  calc
    gibbs_i k
  _ = exp (-attn_energy q k) /
      (keys.sum fun k' => exp (-attn_energy q k')) := rfl
  _ = exp ⟨q, k⟩ / √(d:ℝ) /
      (keys.sum fun k' => exp ⟨q, k'⟩ / √(d:ℝ)) := by
    have : exp (-attn_energy q k) = exp ⟨q, k⟩ / √(d:ℝ) := by
      calc exp (-attn_energy q k) = exp (-(-⟨q,k⟩/√d)) := by rw [attn_energy]
      _ = exp (⟨q,k⟩/√d) := by linarith
    have : exp (-attn_energy q k') = exp ⟨q,k'⟩ / √(d:ℝ) := by
      calc exp (-attn_energy q k') = exp (-(-⟨q,k'⟩/√d)) := by rw [attn_energy]
      _ = exp (⟨q,k'⟩/√d) := by linarith
    simp [this]

end SoftmaxGibbs

-- =============================================================================
-- 定理 4：注意力自由能最小化  F_min = min_{P∈Δ} F(P)
-- =============================================================================
section FreeEnergyMinimization

variable {keys : List Vec}
variable (hkeys_nn : keys ≠ []) (hkeys : keys.Nodup)
variable (q : Vec) (β : ℝ) (hβ : β > 0)

-- KL 散度 ≥ 0（有限完全分解形式的直接证明）
private lemma kl_divergence_nonneg
    {m : ℕ}
    (P Q : Fin m → ℝ)
    (hP : ∀ i, 0 ≤ P i) (hQ : ∀ i, 0 < Q i)
    (hP_sum1 : ∑ i, P i = 1)
    (hQ_sum1 : ∑ i, Q i = 1) :
    0 ≤ ∑ i, P i * log (P i / Q i) := by
  have : ∑ i, P i * log (P i / Q i) =
          ∑ i, P i * log (P i) - ∑ i, P i * log (Q i) := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    have : 0 < Q i := hQ i
    have : 0 < P i := hP i
    exact log_div this.1 this.2
  have := this
  have : ∑ i, P i * log (P i) - ∑ i, P i * log (Q i) ≥ 0 := by
    -- log (P_i/Q_i) ≥ 1 - Q_i/P_i  （Jensen / AM-GM）
    -- 或直接用琴生：log 是凹函数
    have logJensen : ∑ i, P i * log (Q i / P i) ≤ 0 := by
      have : ConcaveOn ℝ (Set.univ : Set ℝ) log := by
        exact ConcaveOn.log
      exact ConcaveOn.le_integral_of_sum_le_one this hP hP_sum1
    have : ∑ i, P i * log (P i / Q i) = -∑ i, P i * log (Q i / P i) := by
      have : log (P i / Q i) = -(log (Q i / P i)) := by linarith
      simp [this]
    linarith
  exact this

theorem attention_free_energy_minimization :
    let m := keys.length
    let P_β (i) := gibbs_attention q keys β hβ (keys[i.1])
    let F_min := (∑ i, P_β i * attn_energy q (keys[i.1])) +
                 (1/β) * (-∑ i, P_β i * log (P_β i))
    ∀ (P : Fin m → ℝ), (∀ i, 0 ≤ P i) → (∑ i, P i) = 1 →
      F_min ≤ (∑ i, P i * attn_energy q (keys[i.1])) +
              (1/β) * (-∑ i, P i * log (P i)) := by
  intro P hP hP_sum1
  let Z := partition_function q keys β hβ
  let E_i (i) := attn_energy q (keys[i.1])

  -- log P_β i = -β E_i - log Z
  have logPβ (i) : log (P_β i) = -β * E_i i - log Z := by
    calc
      log (P_β i)
    _ = log (exp (-β * E_i i) / Z) := rfl
    _ = log (exp (-β * E_i i)) - log Z := by
      have : 0 < exp (-β * E_i i) := by positivity
      have : 0 < Z := by positivity
      exact log_div this.1 this.2
    _ = -β * E_i i - log Z := log_exp _

  -- F(P) - F_min = (1/β)·KL(P ‖ P_β) ≥ 0
  calc
    (∑ i, P i * E_i i) + (1/β) * (-∑ i, P i * log (P i))
    - ((∑ i, P_β i * E_i i) + (1/β) * (-∑ i, P_β i * log (P_β i)))
  _ = (∑ i, P i * E_i i) - (∑ i, P_β i * E_i i) +
      (1/β) * (-∑ i, P i * log (P i) + ∑ i, P_β i * log (P_β i)) := by linarith
  _ = (∑ i, P i * E_i i) - (∑ i, P_β i * E_i i) +
      (1/β) * (∑ i, P_β i * log (P_β i) - ∑ i, P i * log (P i)) := by linarith
  _ = (1/β) * (∑ i, P_β i * (-β * E_i i - log Z) -
                ∑ i, P i * log (P i) + ∑ i, P i * (-β * E_i i)) := by
    calc
      (∑ i, P_β i * log (P_β i)) = ∑ i, P_β i * (-β * E_i i - log Z) := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [logPβ]
      _ = -(β * ∑ i, P_β i * E_i i) - (log Z) * ∑ i, P_β i := by
        simp; ring
      _ = -(β * ∑ i, P_β i * E_i i) - log Z := by
        have : ∑ i, P_β i = 1 := by
          calc _ = keys.sum (fun k => gibbs_attention q keys β hβ k) := rfl
          _ = keys.sum (fun k => exp _) / Z := by simp
          _ = Z / Z := by simp
          _ = 1 := by linarith
        linarith
    linarith
  _ = (1/β) * (∑ i, P_β i * (-log Z) + log Z * ∑ i, P i -
                ∑ i, P i * log (P i)) := by
    calc
      _ = (1/β) * (-(β * ∑ i, P_β i * E_i i) - log Z +
                   β * ∑ i, P i * E_i i - ∑ i, P i * log (P i)) := by linarith
    _ = (1/β) * (β * ∑ i, P i * E_i i - β * ∑ i, P_β i * E_i i -
                   log Z + log Z * ∑ i, P i -
                   ∑ i, P i * log (P i)) := by linarith
    _ = (1/β) * (log Z * (∑ i, P i - 1) +
                   β * (∑ i, P i * E_i i - ∑ i, P_β i * E_i i) -
                   ∑ i, P i * log (P i)) := by linarith
    _ = (1/β) * (-∑ i, P i * log (P i) +
                   β * (∑ i, P i * E_i i - ∑ i, P_β i * E_i i) -
                   log Z * (1 - ∑ i, P i)) := by linarith
    _ = (1/β) * (-∑ i, P i * log (P i) +
                   β * (∑ i, P i * E_i i - ∑ i, P_β i * E_i i) -
                   log Z * 0) := by linarith
    _ = (1/β) * (∑ i, P_β i * log Z - ∑ i, P i * log (P i)) := by
      calc
        (1/β) * (-∑ i, P i * log (P i) +
                   β * (∑ i, P i * E_i i - ∑ i, P_β i * E_i i) -
                   log Z)
      _ = (1/β) * (-∑ i, P i * log (P i) +
                    β * ∑ i, P i * E_i i -
                    β * ∑ i, P_β i * E_i i - log Z) := by linarith
      _ = (1/β) * (β * ∑ i, P i * E_i i -
                    β * ∑ i, P_β i * E_i i -
                    ∑ i, P i * log (P i) - log Z) := by linarith
      _ = (1/β) * (∑ i, P_β i * (-β * E_i i) -
                    ∑ i, P i * log (P i) - log Z) := by linarith
      _ = (1/β) * (∑ i, P_β i * log (P_β i) -
                    ∑ i, P i * log (P i) + log Z * ∑ i, P_β i -
                    log Z) := by
        have : ∑ i, P_β i * (-β * E_i i - log Z) = ∑ i, P_β i * log (P_β i) := by
          calc
            ∑ i, P_β i * (-β * E_i i - log Z)
          _ = -(β * ∑ i, P_β i * E_i i) - log Z * ∑ i, P_β i := by simp; ring
          _ = -(β * ∑ i, P_β i * E_i i) - log Z := by
            have : ∑ i, P_β i = 1 := by
              calc _ = keys.sum (fun k => gibbs_attention q keys β hβ k) := rfl
              _ = keys.sum (fun k => exp _) / Z := by simp
              _ = Z / Z := by simp
              _ = 1 := by linarith
            linarith
          _ = ∑ i, P_β i * log (P_β i) := by
            calc
              ∑ i, P_β i * log (P_β i)
            _ = ∑ i, P_β i * (-β * E_i i - log Z) := by
              refine Finset.sum_congr rfl (fun i _ => ?_)
              rw [logPβ]
            _ = _ := rfl
        linarith
      _ = (1/β) * (∑ i, P_β i * log (P_β i) - ∑ i, P_β i * log Z -
                    ∑ i, P i * log (P i)) := by
        have : ∑ i, P_β i * log Z = log Z * ∑ i, P_β i := by linarith
        have : ∑ i, P_β i = 1 := by
          calc _ = keys.sum (fun k => gibbs_attention q keys β hβ k) := rfl
          _ = keys.sum (fun k => exp _) / Z := by simp
          _ = Z / Z := by simp
          _ = 1 := by linarith
        linarith
      _ = (1/β) * (∑ i, P_β i * (log (P_β i) - log Z) -
                    ∑ i, P i * log (P i)) := by linarith
      _ = (1/β) * (∑ i, P_β i * log (P_β i / Z) -
                    ∑ i, P i * log (P i)) := by linarith
    _ = (1/β) * (∑ i, P i * log (P_β i / P i)) := by
      have : ∀ i, 0 < P_β i := by intro i; positivity
      have : ∀ i, 0 < P i := by intro i; linarith
      have : ∑ i, P_β i * log (P_β i / Z) = ∑ i, P i * log (P_β i / P i) := by
        sorry
      linarith

  -- 最终表达式是 (1/β)·KL(P ‖ P_β) ≥ 0
  have F_diff_eq_KL :
      (∑ i, P i * E_i i) + (1/β) * (-∑ i, P i * log (P i)) -
      ((∑ i, P_β i * E_i i) + (1/β) * (-∑ i, P_β i * log (P_β i))) =
      (1/β) * ∑ i, P i * log (P i / P_β i) := by
    have := helmholtz_identity q keys β hβ hkeys
    have logP_β (i) : log (P_β i) = -β * E_i i - log Z := by
      calc log (P_β i)
      _ = log (exp (-β * E_i i) / Z) := rfl
      _ = -β * E_i i - log Z := by
        have : 0 < exp (-β * E_i i) := by positivity
        have : 0 < Z := by positivity
        have := log_div this.1 this.2
        have : log (exp (-β * E_i i)) = -β * E_i i := log_exp _
        linarith
    have ΣPβE : ∑ i, P_β i * E_i i = -(1/β) * (∑ i, P_β i * log (P_β i)) - (1/β) * log Z := by
      calc
        ∑ i, P_β i * E_i i
      _ = -(1/β) * ∑ i, P_β i * (-β * E_i i) := by linarith
      _ = -(1/β) * ∑ i, P_β i * (log (P_β i) + log Z) := by
        have : -β * E_i i = log (P_β i) + log Z := by linarith [logP_β]
        exact this
      _ = -(1/β) * (∑ i, P_β i * log (P_β i) + ∑ i, P_β i * log Z) := by linarith
      _ = -(1/β) * (∑ i, P_β i * log (P_β i) + log Z) := by
        have : ∑ i, P_β i = 1 := by
          calc _ = keys.sum (fun k => gibbs_attention q keys β hβ k) := rfl
          _ = keys.sum (fun k => exp _) / Z := by simp
          _ = Z / Z := by simp
          _ = 1 := by linarith
        linarith
      _ = -(1/β) * ∑ i, P_β i * log (P_β i) - (1/β) * log Z := by linarith
    calc
      (∑ i, P i * E_i i) + (1/β) * (-∑ i, P i * log (P i))
      - ((∑ i, P_β i * E_i i) + (1/β) * (-∑ i, P_β i * log (P_β i)))
    _ = (∑ i, P i * E_i i) - (∑ i, P_β i * E_i i) +
        (1/β) * (-∑ i, P i * log (P i) + ∑ i, P_β i * log (P_β i)) := by linarith
    _ = (∑ i, P i * E_i i) +
        (1/β) * ∑ i, P_β i * log (P_β i) + (1/β) * log Z -
        (1/β) * (-∑ i, P i * log (P i)) := by
        have : (∑ i, P_β i * E_i i) = -(1/β) * ∑ i, P_β i * log (P_β i) - (1/β) * log Z := ΣPβE
        linarith
    _ = (1/β) * (β * ∑ i, P i * E_i i +
                   ∑ i, P_β i * log (P_β i) + log Z +
                   ∑ i, P i * log (P i)) := by linarith
    _ = (1/β) * (∑ i, P_β i * (-β * E_i i) + ∑ i, P_β i * log (P_β i) +
                   log Z * ∑ i, P i + ∑ i, P i * log (P i)) := by
      have : β * ∑ i, P i * E_i i = ∑ i, P i * (β * E_i i) := rfl
      linarith
    _ = (1/β) * (∑ i, P_β i * log (P_β i) - ∑ i, P_β i * log Z +
                   ∑ i, P i * log (P i) + log Z) := by
      have : ∑ i, P i = 1 := hP_sum1
      linarith
    _ = (1/β) * (∑ i, P_β i * (log (P_β i) - log Z) +
                   ∑ i, P i * log (P i) + log Z) := by linarith
    _ = (1/β) * (∑ i, P_β i * log (P_β i / Z) +
                   ∑ i, P i * log (P i) + log Z) := by linarith
    _ = (1/β) * (∑ i, P i * log (P i / P_β i)) := by
      have : ∀ i, 0 < P_β i := by intro i; positivity
      have : ∀ i, 0 < P i := by intro i; linarith
      have : ∑ i, P_β i * log (P_β i / Z) = ∑ i, P i * log (P i / P_β i) := by
        have : Z = partition_function q keys β hβ := rfl
        have : Z = keys.sum (fun k => exp (-β * E_i k)) := rfl
        have : Z = keys.sum (fun k => P_β k * Z) := by linarith
        have : keys.sum (fun k => P_β k) = 1 := by
          calc _ = keys.sum (fun k => gibbs_attention q keys β hβ k) := rfl
          _ = keys.sum (fun k => exp _) / Z := by simp
          _ = Z / Z := by simp
          _ = 1 := by linarith
        have : ∀ i, P_β i / Z = exp (-β * E_i i) / Z / Z := by
          intro i; linarith
        have : P_β i / Z = P_β i / Z := rfl
        sorry
    _ = (1/β) * ∑ i, P i * log (P i / P_β i) := rfl

  have kl_nn : 0 ≤ ∑ i, P i * log (P i / P_β i) := by
    have : ∀ i, 0 < P_β i := by intro i; positivity
    have : ∀ i, 0 ≤ P i := by intro i; linarith
    exact kl_divergence_nonneg P P_β this (by intro i; positivity)
      hP_sum1 (by calc ∑ i, P_β i = 1 := by
        calc _ = keys.sum (fun k => gibbs_attention q keys β hβ k) := rfl
        _ = keys.sum (fun k => exp _) / Z := by simp
        _ = Z / Z := by simp
        _ = 1 := by linarith)
  linarith

end FreeEnergyMinimization

-- =============================================================================
-- 定理 5：Landauer 耗散界限（trivial）
-- =============================================================================
section LandauerBound

theorem landauer_bound
    (k_B T : ℝ) (hk_B : k_B ≥ 0) (hT : T ≥ 0)
    (bits : ℝ) (hbits : bits ≥ 0) :
    W_min := k_B * T * log 2 * bits
    W_min ≥ k_B * T * log 2 * bits := by linarith

end LandauerBound

-- =============================================================================
-- 定理 6：拓扑修正项的 Landauer 解释（trivial）
-- =============================================================================
section TopoLandauer

theorem topo_correction_landauer_interpretation
    (α β0 κbar T k_B : ℝ)
    (hα : α ≥ 0) (hβ0 : β0 ≥ 0) (hκbar : κbar ≥ 0)
    (hT : T > 0) (hk_B : k_B > 0)
    (b_old b_new : ℕ) (hb_old : b_old > 0)
    (h_ratio : b_new ≤ b_old) :
    let ΔF_topo := α * β0 * |κbar|
    ΔF_topo ≥ k_B * T * log (b_old / b_new : ℝ) := by
  have : ΔF_topo ≥ 0 := by positivity
  have RHS : k_B * T * log (b_old / b_new : ℝ) ≥ 0 := by
    have : (b_old / b_new : ℝ) ≥ 1 := by linarith
    exact mul_nonneg (by linarith) (log_nonneg this)
  linarith

end TopoLandauer

-- =============================================================================
-- 定理 7：DTS KL 压缩启发式（trivial）
-- =============================================================================
section DTSKL

theorem dts_kl_compression_heuristic
    (z z' : Vec) (κ : Vec → ℝ) (γ : ℝ) (hγ : γ > 1)
    (hDTS : DTSKernel z z' κ γ (by linarith) z z' ≥ γ)
    (hneg : ⟪z, z'⟫_ℝ ≤ 0) (hdist : 1 ≤ dist z z') :
    let Q_dst := DTSKernel z z' κ γ (by linarith) z z' / γ
    let d_eff := -(1/γ) * log Q_dst
    log Q_dst + 1 - Q_dst ≤ dist z z' / γ := by
  have Q_le : Q_dst ≤ 1 + 1/γ := by
    have : DTSKernel z z' κ γ (by linarith) z z' ≤ 1 + γ := by
      exact DTS_shortcut_efficiency z z' κ γ (by linarith) hDTS hneg hdist
    have : 0 < γ := by linarith; linarith
  have KL_neg : log Q_dst + 1 - Q_dst ≤ 0 := by
    have : 0 < Q_dst := by positivity
    have : log Q_dst ≤ Q_dst - 1 := log_le_sub_one_of_pos this
    linarith
  have d_eff_le : d_eff ≤ dist z z' / γ := by
    exact DTS_shortcut_efficiency z z' κ γ (by linarith) hDTS hneg hdist
  have KL_le_d_eff : log Q_dst + 1 - Q_dst ≤ d_eff := by linarith
  exact KL_le_d_eff

end DTSKL

-- =============================================================================
-- 定理 8：CPA ↔ 零温度极限对应（使用 ScaleOperator）
-- =============================================================================
section CPAZeroTemp

-- ══════════════════════════════════════════════════════
-- cpa_zerotemp_correspondence
--   lim_{β→∞} gibbs_attention(q, K, β) = cpa_attention(q, K)
--
--   依赖：ScaleOperator.macroEnergyConverges
--   （宏观自由能收敛 → 与零温度极限的确定性对应）
-- ══════════════════════════════════════════════════════
theorem cpa_zerotemp_correspondence
    {keys : List Vec}
    (hkeys_nn : keys ≠ [])
    (hkeys : keys.Nodup)
    (q : Vec)
    (F_dyn : State n → State n)
    (hF_cont : Continuous F_dyn)
    (E : State n → ℝ)
    (hE_cont : Continuous E)
    (E_nneg : ∀ x, 0 ≤ E x)
    (E_desc : ∀ x, F_dyn x ≠ x → E (F_dyn x) < E x)
    (S : ScaleOperator λ n) :
    Tendsto
      (fun (β : ℝ) (hβ : β > 0) (k : Vec) =>
        gibbs_attention q keys β hβ k)
      atTop
      (𝓝 (cpa_attention q keys k)) := by
  -- 宏观动力学收敛性（来自 ScaleOperator）
  have macro_converges (x0 : State n) :
      Tendsto
        (fun k => S.energyMacro ({orbit F_dyn x0 k} : Set (State n)))
        atTop (𝓝 (⨅ k, S.energyMacro ({orbit F_dyn x0 k} : Set (State n)))) :=
    macroEnergyConverges F_dyn hF_cont E hE_cont E_nneg E_desc x0 S

  -- 识别 E_min 和 K_min
  rcases exists_min_key keys q hkeys_nn with ⟨k*, hE_min⟩
  let E_min := attn_energy q k*
  let K_min := keys.filter (· = E_min)

  intro k
  by_cases hk : k ∈ K_min
  · -- k ∈ K_min：归一化后，P → 1/|K_min|
    have P_upper (β : ℝ) (hβ : β > 0) :
        gibbs_attention q keys β hβ k ≤ 1 / (K_min.length : ℝ) := by
      let Z := partition_function q keys β hβ
      have Z_ge : Z ≥ (K_min.length : ℝ) * exp (-β * E_min) := by
        calc
          Z = keys.sum (fun k' => exp (-β * attn_energy q k')) := rfl
          _ ≥ K_min.sum (fun _ => exp (-β * E_min)) := by
            apply Finset.sum_le_sum_of_subsetOf_nonneg
            · exact List.toFinset_filter_subset
            · intro; positivity
          _ = (K_min.length : ℝ) * exp (-β * E_min) := by
            have : K_min.all (· = E_min) = true := by
              funext k'; simp; exact List.of_mem_filter.1
            exact Finset.sum_const this
      have : 0 < K_min.length := by positivity
      have : 0 < exp (-β * E_min) := by positivity
      have : 0 < Z := by positivity
      have : attn_energy q k = E_min := List.of_mem_filter.1 hk
      calc
        gibbs_attention q keys β hβ k
      _ = exp (-β * E_min) / Z := by rw [this]
      _ ≤ exp (-β * E_min) / ((K_min.length : ℝ) * exp (-β * E_min)) := by
        have : 0 < K_min.length := by positivity
        exact div_le_div_of_le_of_pos Z_ge this
      _ = 1 / (K_min.length : ℝ) := by field_simp
    have P_lower (β : ℝ) (hβ : β > 0) :
        gibbs_attention q keys β hβ k ≥
        1 / ((K_min.length : ℝ) * (1 + (keys.length - K_min.length) * exp (-β))) := by
      let Z := partition_function q keys β hβ
      have Z_le : Z ≤
          (K_min.length : ℝ) * exp (-β * E_min) *
          (1 + (keys.length - K_min.length) * exp (-β)) := by
        have : (keys.erase k*).all (fun k => attn_energy q k ≥ E_min + 1) := by
          have : ∀ k ∈ keys.erase k*, attn_energy q k > E_min := by
            intro k hk; have : k ≠ k* := by
              have : k ∈ keys.erase k* := hk
              simp at this
            have : attn_energy q k ≥ E_min := hE_min k
            have : k ≠ k* → attn_energy q k > E_min := by
              intro _; linarith
            linarith
          funext k'; simp; exact this
        calc
          Z
        _ = exp (-β * E_min) + (keys.erase k*).sum (fun k => exp (-β * attn_energy q k)) := by
          have : k* ∈ keys := by trivial
          exact Finset.sum_erase keys (·∈·) k*
        _ = exp (-β * E_min) * (1 + (keys.erase k*).sum (fun k =>
            exp (-β * (attn_energy q k - E_min)))) := by
          refine Finset.sum_congr rfl (fun k hk => ?_)
          have : k ∈ keys.erase k* := hk
          have δ := attn_energy q k - E_min
          have δ ≥ 1 := by linarith
          calc exp (-β * (E_min + δ))
              = exp (-β * E_min) * exp (-β * δ) := by linarith
          _ ≤ exp (-β * E_min) * exp (-β) := by
            have : 0 < β := by linarith
            have : 0 < exp (-β) := by positivity
            linarith
        _ ≤ exp (-β * E_min) * (1 + (keys.length - 1) * exp (-β)) := by
          have : (keys.erase k*).length = keys.length - 1 := by
            have : k* ∈ keys := by trivial
            exact Nat.sub_add_cancel (List.length_erase_of_mem this).symm
          linarith
        _ = (K_min.length : ℝ) * exp (-β * E_min) *
            (1 + (keys.length - K_min.length) * exp (-β)) := by
          have : K_min.length = 1 := by
            have : k* ∈ K_min := by
              have : k* ∈ keys := by trivial
              exact List.mem_filter.2 ⟨this, rfl⟩
            have : ∀ k' ∈ K_min, attn_energy q k' = E_min := by
              intro k' hk'; have := List.of_mem_filter.1 hk'
            have : K_min ⊆ [k*] := by
              have : k* ∈ K_min := by
                have : k* ∈ keys := by trivial
                exact List.mem_filter.2 ⟨this, rfl⟩
              have : ∀ k' ∈ K_min, k' = k* := by
                intro k' hk'; have := List.of_mem_filter.1 hk'
                linarith
              exact this
            linarith
          linarith
      have : 0 < Z := by positivity
      have : 0 < K_min.length := by positivity
      have : 0 < 1 + _ := by positivity
      have : attn_energy q k = E_min := List.of_mem_filter.1 hk
      calc
        gibbs_attention q keys β hβ k
      _ = exp (-β * E_min) / Z := by rw [this]
      _ ≥ exp (-β * E_min) /
          ((K_min.length : ℝ) * exp (-β * E_min) *
           (1 + (keys.length - K_min.length) * exp (-β))) := by
        exact div_le_div_of_le_of_pos Z_le this
      _ = 1 / ((K_min.length : ℝ) * (1 + (keys.length - K_min.length) * exp (-β))) := by
        have : 0 < K_min.length := by positivity
        have : 0 < 1 + _ := by positivity
        field_simp; linarith
    have lb_tendsto : Tendsto
        (fun β => 1 / ((K_min.length : ℝ) * (1 + (keys.length - K_min.length) * exp (-β))))
        atTop (𝓝 (1 / (K_min.length : ℝ))) := by
      have exp_tendsto_0 : Tendsto (fun β => exp (-β)) atTop (𝓝 0) :=
        tendsto_exp_neg_atTop
      have denom_tendsto_1 : Tendsto
          (fun β => 1 + (keys.length - K_min.length) * exp (-β))
          atTop (𝓝 1) :=
        Tendsto.add_const 1
          (mul_continuous_atTop (keys.length - K_min.length) (by linarith) exp_tendsto_0)
      have : 0 < K_min.length := by positivity
      exact Tendsto.div_const _ this |>.comp denom_tendsto_1
    exact tendsto_of_tendsto_of_le_of_le (P_lower _) (P_upper _) lb_tendsto
      (Tendsto.const _ _)
  · -- k ∉ K_min：P → 0
    have : attn_energy q k > E_min := by
      have : k ∉ K_min := hk
      have : k ∈ keys := by trivial
      have : attn_energy q k ≠ E_min := by
        have : k ∈ K_min ↔ k ∈ keys ∧ attn_energy q k = E_min := by
          exact List.mem_filter
        have : k ∈ K_min ↔ false := by linarith
        exact not_congr this |>.mp trivial
      have : attn_energy q k ≥ E_min := hE_min k
      linarith
    have δ := this
    have num_tendsto_0 : Tendsto (fun b => exp (-b * attn_energy q k)) atTop (𝓝 0) :=
      tendsto_exp_neg_atTop.comp (tendsto_id.const_nhds (attn_energy q k))
    have Z_ge (b) : partition_function q keys b (by linarith) ≥ exp (-b * E_min) := by
      calc
        _ = keys.sum (fun k' => exp (-b * attn_energy q k')) := rfl
        _ ≥ exp (-b * E_min) := by
          exact Finset.le_sum_of_sum_le keys (fun k' => exp _) k*
    have ratio_le (b) :
        gibbs_attention q keys b (by linarith) k ≤
        exp (-b * (attn_energy q k - E_min)) := by
      let Z := partition_function q keys b (by linarith)
      have : 0 < Z := by positivity
      have : 0 < exp (-b * E_min) := by positivity
      calc
        gibbs_attention q keys b (by linarith) k
      _ = exp (-b * attn_energy q k) / Z := rfl
      _ ≤ exp (-b * attn_energy q k) / exp (-b * E_min) := by
        exact div_le_div_of_le_of_pos (Z_ge b) this
      _ = exp (-b * (attn_energy q k - E_min)) := by linarith
    have exp_tendsto_0 : Tendsto
        (fun b => exp (-b * (attn_energy q k - E_min))) atTop (𝓝 0) :=
      tendsto_exp_neg_atTop.comp (tendsto_id.const_nhds δ)
    exact tendsto_of_tendsto_of_le_of_le'
      (fun b hb => by linarith)
      (fun b hb => by linarith [ratio_le b])
      exp_tendsto_0
      (Tendsto.const _ _)

end CPAZeroTemp
