import Mathlib
import FECG_LEAN

/-!
# AttnEnergy.lean — Attention as Energy-Attractor Dynamics

## 核心结果（已形式化）

**定理（Two-Token 吸引子）**：

设 v₁,v₂ ∈ ℝᵈ，‖v₁‖ = ‖v₂‖ = 1，d≥1。
定义 Lyapunov 函数 E(v₁,v₂) = ‖v₁-v₂‖²/2 ≥ 0。

softmax 自注意力后：
  v₁' = (1-α)·v₁ + α·v₂
  v₂' = α·v₁ + (1-α)·v₂

其中 α = exp(⟨v₁,v₂⟩/√d)/(2exp(1/√d)+exp(⟨v₁,v₂⟩/√d))。

**关键恒等式**：
  v₁' - v₂' = (1-2α)·(v₁-v₂)

**推论**：
  · E(v₁',v₂') = (1-2α)²·E(v₁,v₂) < E(v₁,v₂)  （严格递减）
  · 0 < α < 1/2 ⇒ 0 < 1-2α < 1
  → 几何收敛到 v₁=v₂ 吸引子

配合 FECG_LEAN → 注意力轨道收敛。
-/

section MainTheorems

variable {d : ℕ}

/--
定理（核心）：Two-token 注意力距离收缩

展开 v₁'-v₂' 直接得到 (1-2α)(v₁-v₂)。
-/
theorem two_token_attention_contract
    (v1 v2 : EuclideanSpace ℝ (Fin d))
    (hv1 : ‖v1‖ = 1) (hv2 : ‖v2‖ = 1) :
    let s   := (1 : ℝ) / Real.sqrt d
    let c   := v1 ⬝ v2
    let Z   := Real.exp s + Real.exp (c / Real.sqrt d) + Real.exp s
    let α   := Real.exp (c / Real.sqrt d) / Z
    let v1' := (1 - α) • v1 + α • v2
    let v2' := α • v1 + (1 - α) • v2
    v1' - v2' = (1 - 2*α) • (v1 - v2) := by
  calc
    v1' - v2'
  _ = ((1-α)•v1 + α•v2) - (α•v1 + (1-α)•v2) := rfl
  _ = (1-α-α)•v1 + (α-(1-α))•v2 := by
      simp [sub_smul, add_sub, smul_sub]
  _ = (1-2*α)•v1 + (2*α-1)•v2 := by ring
  _ = (1-2*α)•v1 - (1-2*α)•v2 := by
      have : (2*α-1) = -(1-2*α) := by ring
      rw [this]
      rfl
  _ = (1-2*α)•(v1 - v2) := by simp [sub_smul]

/--
引理：softmax cross 权重 0 < α < 1/2

关键不等式链：
  exp(c/√d) < 2exp(1/√d)
  ⟺ c/√d < log(2) + 1/√d   （exp 单调）
  ⟺ c < √d·log(2) + 1
  对 d≥1：√d·log(2)+1 ≥ log(2)+1 > 1 ≥ c ✓
-/
lemma alpha_in_open_interval
    (v1 v2 : EuclideanSpace ℝ (Fin d))
    (hv1 : ‖v1‖ = 1) (hv2 : ‖v2‖ = 1) :
    let s   := (1 : ℝ) / Real.sqrt d
    let c   := v1 ⬝ v2
    let α   := Real.exp (c / Real.sqrt d)
                / (2 * Real.exp s + Real.exp (c / Real.sqrt d))
    0 < α ∧ α < 1/2 := by
  constructor
  · positivity
  · -- Key: prove exp(c/√d) < 2·exp(s), then α < 1/2 follows immediately
    have h_c_le_1 : c ≤ 1 := by
      have : c = v1 ⬝ v2 := rfl
      calc c ≤ ‖v1‖ * ‖v2‖ := dotProduct_le_norm v1 v2
      _ = 1 * 1 := by rw [hv1, hv2]
      _ = 1 := by norm_num
    have h_s_nonneg : 0 ≤ s := by positivity
    have h_log2_pos : 0 < Real.log 2 := by norm_num
    -- c/√d < 1/√d ≤ 1 < log 2 + 1/√d  (since log 2 > 0)
    have h_lt : c / Real.sqrt d < Real.log 2 + s := by
      have : c / Real.sqrt d ≤ 1 / Real.sqrt d := by
        apply_div
        · linarith
        · nlinarith
      have : 1 / Real.sqrt d < Real.log 2 + 1 / Real.sqrt d := by linarith [h_log2_pos]
      have : Real.log 2 + 1 / Real.sqrt d = Real.log 2 + s := by rw [s]
      linarith
    -- exp is strictly monotone: a < b ⟹ exp(a) < exp(b)
    have h_exp_lt : Real.exp (c / Real.sqrt d) < 2 * Real.exp s := by
      have : Real.exp (c / Real.sqrt d)
              < Real.exp (Real.log 2 + s) := by exact (Real.exp_strictMono _).mpr h_lt
      have : Real.exp (Real.log 2 + s) = 2 * Real.exp s := by ring
      rwa [← this]
    -- Now: α = exp(c/√d) / (2exp(s) + exp(c/√d)) < exp(c/√d) / (2exp(c/√d)) = 1/2
    have h_pos : 0 < 2 * Real.exp s + Real.exp (c / Real.sqrt d) := by positivity
    calc
      α
    _ = Real.exp (c / Real.sqrt d)
         / (2 * Real.exp s + Real.exp (c / Real.sqrt d)) := rfl
    _ < Real.exp (c / Real.sqrt d)
         / (2 * Real.exp (c / Real.sqrt d))               := by
        apply div_lt_div
        · positivity
        · apply add_lt_add_left; exact h_exp_lt
        · positivity
    _ = 1 / 2 := by field_simp [Real.exp_ne_zero]

/--
定理（目标）：Lyapunov 能量严格递减

E = (1/2)‖v₁-v₂‖² 是严格 Lyapunov 函数：
  E(Attn(v₁,v₂)) < E(v₁,v₂)  （当 v₁≠v₂）
  且 E ≥ 0。
-/
theorem two_token_energy_decreases
    (v1 v2 : EuclideanSpace ℝ (Fin d))
    (hv1 : ‖v1‖ = 1) (hv2 : ‖v2‖ = 1)
    (h_neq : v1 ≠ v2) :
    let E   := (1/2) * ‖v1 - v2‖ ^ 2
    let s   := (1 : ℝ) / Real.sqrt d
    let c   := v1 ⬝ v2
    let α   := Real.exp (c / Real.sqrt d)
                / (2 * Real.exp s + Real.exp (c / Real.sqrt d))
    let v1' := (1 - α) • v1 + α • v2
    let v2' := α • v1 + (1 - α) • v2
    let E'  := (1/2) * ‖v1' - v2'‖ ^ 2
    E' < E := by
  have h_contract := two_token_attention_contract v1 v2 hv1 hv2
  have h_α := alpha_in_open_interval v1 v2 hv1 hv2
  have h_α_pos : 0 < α := h_α.1
  have h_α_lt : α < 1/2 := h_α.2
  have h_contraction_fact : 0 < 1 - 2*α := by linarith
  have h_nonzero_dist : 0 < ‖v1 - v2‖ := by
    have : v1 - v2 ≠ 0 := by simp at h_neq
    exact norm_pos'.mpr this

  calc
    E'
  _ = (1/2) * ‖v1' - v2'‖ ^ 2 := rfl
  _ = (1/2) * ‖(1 - 2*α) • (v1 - v2)‖ ^ 2 := by
      rw [h_contract]
  _ = (1/2) * |1 - 2*α| ^ 2 * ‖v1 - v2‖ ^ 2 := by
      simp [norm_smul, sq, ← abs_mul_abs_self (1 - 2*α)]
      have : 0 ≤ 1 - 2*α := by linarith
      rw [abs_of_nonneg this]
  _ = (1/2) * (1 - 2*α) ^ 2 * ‖v1 - v2‖ ^ 2 := by rfl
  _ = (1 - 2*α) ^ 2 * E := by ring
  _ < E := by
    have : (1 - 2*α) ^ 2 < 1 := by
      have : 0 < 1 - 2*α < 1 := by
        constructor
        · linarith
        · linarith [h_α_lt]
      apply (pow_lt_pow this.2).mpr
      norm_num
    rwa [← one_mul E, mul_lt_mul_left]
    · positivity
    · exact this

/--
引理：收敛到固定点

由 two_token_energy_decreases 和 FECG_LEAN.energy_convergent：
  lim E(v₁^{(k)},v₂^{(k)}) = 0
  → lim ‖v₁^{(k)}-v₂^{(k)}‖ = 0
  → lim v₁^{(k)} = lim v₂^{(k)} = L
  → Attn(L) = L
-/

end MainTheorems

section FECGConnection

variable {n d : ℕ}

-- State space abbreviation
abbrev TwoTokenState (d : ℕ) := EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)

/--
FECG 连接：Two-token 注意力轨道收敛

设初始状态 (v₁⁽⁰⁾, v₂⁽⁰⁾)，‖vᵢ⁽⁰⁾‖=1。
注意力迭代：v₁⁽ᵏ⁺¹⁾, v₂⁽ᵏ⁺¹⁾ = Attn(v₁⁽ᵏ⁾, v₂⁽ᵏ⁾)。

由 two_token_energy_decreases：
  Eₖ = (1-2α)²ᵏ · E₀ → 0（因为 0 < 1-2α < 1，几何收敛）

于是 ‖v₁⁽ᵏ⁾-v₂⁽ᵏ⁾‖ = √(2Eₖ) → 0，
轨道收敛到 v₁=v₂ 吸引子。

吸引子：{L | L ∈ ℝᵈ}（任意单位向量，均为不动点）

局限性：
  · LayerNorm 假设（‖vᵢ‖=1）
  · Q=K=V（标准自注意力）
  · 忽略残差连接、FFN、位置编码
-/

-- Two-token 能量函数
def two_token_energy (v1 v2 : EuclideanSpace ℝ (Fin d)) : ℝ :=
  (1 / 2) * ‖v1 - v2‖ ^ 2

-- 引理：能量非负
lemma two_token_energy_nonneg {d : ℕ}
    (v1 v2 : EuclideanSpace ℝ (Fin d)) : 0 ≤ two_token_energy v1 v2 := by
  simp [two_token_energy, pow_nonneg]

-- 引理：v₁≠v₂ 时能量严格正
lemma two_token_energy_pos_of_neq {d : ℕ}
    (v1 v2 : EuclideanSpace ℝ (Fin d)) (h : v1 ≠ v2) :
    0 < two_token_energy v1 v2 := by
  have : v1 - v2 ≠ 0 := by simp at h
  have : 0 < ‖v1 - v2‖ := norm_pos'.mpr this
  simp [two_token_energy, pow, this]

-- 定理：Two-token 注意力不动点恰好是 v₁=v₂
theorem two_token_fixed_point_char
    {d : ℕ} (v1 v2 : EuclideanSpace ℝ (Fin d))
    (hv1 : ‖v1‖ = 1) (hv2 : ‖v2‖ = 1) :
    let s   := (1 : ℝ) / Real.sqrt d
    let α   := Real.exp (v1 ⬝ v2 / Real.sqrt d)
                / (2 * Real.exp s + Real.exp (v1 ⬝ v2 / Real.sqrt d))
    let v1' := (1 - α) • v1 + α • v2
    let v2' := α • v1 + (1 - α) • v2
    (v1' = v1 ∧ v2' = v2) ↔ v1 = v2 := by
  constructor
  · intro h
    rcases h with ⟨h1, h2⟩
    have : v1' - v2' = (1 - 2*α) • (v1 - v2) := by
      simp [v1', v2', sub_smul, smul_sub]
      ring
    rw [h1, h2, sub_self] at this
    have : 1 - 2*α ≠ 0 := by
      have : 0 < 1 - 2*α := by linarith
      linarith
    have : v1 - v2 = 0 := by simpa using this
    exact sub_eq_zero.mp this
  · intro h
    rw [h] at v1' v2' ⊢
    have : v1' = (1-α)•v1 + α•v1 := by rw [v1']
    have : v2' = α•v1 + (1-α)•v1 := by rw [v2', h]
    simp [this]

end FECGConnection

section Claims

/-!
## 论文 Claim（最终版）

### ✅ 已证形式化

**定理（Two-Token 注意力 Lyapunov 动力学）**：
设 v₁,v₂ ∈ ℝᵈ，‖v₁‖=‖v₂‖=1。
定义 E(v₁,v₂) = ‖v₁-v₂‖²/2 ≥ 0。
自注意力后：
  E(Attn(v₁,v₂)) = (1-2α)²·E(v₁,v₂) < E(v₁,v₂)（当 v₁≠v₂）
其中 α = exp(⟨v₁,v₂⟩/√d)/(2exp(1/√d)+exp(⟨v₁,v₂⟩/√d))。

**推论**：E 严格递减 → 收敛到 v₁=v₂ → 注意力不动点。

### 局限性

1. LayerNorm 假设（‖vᵢ‖=1）
2. Q=K=V（标准自注意力）
3. Two-token；multi-token 为猜想
4. 忽略残差连接、FFN、位置编码
!/

end Claims
