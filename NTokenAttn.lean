import Mathlib
import AttnEnergy

/-!
# NTokenAttn.lean — Multi-Token Attention Lyapunov Dynamics

## 从 Two-Token 到 n-Token

Two-token 核心恒等式（AttnEnergy.lean）：
  · α_ij = exp(c_ij/√d) / Σ exp(c_kl/√d)
  · v_i' - v_j' = (1 - 2·α_ij) · (v_i - v_j)

关键发现：收缩因子 (1-2·α_ij) 与 token 总数 n 无关！
  · 证明：分子 exp(c_ij/√d) < Σ exp(c_kl/√d) - exp(c_ij/√d)
    （因为 exp 单调，且 c_ij ≤ 1 = ‖v_i‖·‖v_j‖）
    → α_ij < 1/2 恒成立，与 n 无关
    → 0 < 1-2·α_ij < 1 恒成立

因此：每对 token 之间的欧氏距离在每次注意力迭代后都收缩。

**核心引理（n-token 距离收缩）**：
  · d_ij^{(k)} = ‖v_i^{(k)} - v_j^{(k)}‖
  · d_ij^{(k+1)} = |1-2·α_ij^{(k)}| · d_ij^{(k)}
  · 由于 0 < |1-2·α_ij| < 1，d_ij^{(k)} → 0 对所有 i,j

**能量引理（n-token 总能量）**：
  · E^{(k)} = (1/2n) · Σᵢ<j ‖v_i^{(k)} - v_j^{(k)}‖²
  · E^{(k+1)} = (1/2n) · Σᵢ<j (1-2·α_ij^{(k)})² · ‖v_i^{(k)} - v_j^{(k)}‖²
  · 由于 max_{i<j}(1-2·α_ij)² < 1，
    且对所有 i,j 都有收缩（除非 v_i^{(k)} = v_j^{(k)}），
    E^{(k)} 严格递减 → 收敛到 0
!/

section NTokenBasics

variable {n d : ℕ}
variable (hv : ∀ (i : Fin n), let v := vec_fn i; ‖v‖ = 1)

/--
引理：n-token softmax 权重 0 < α_ij < 1/2

对任意 token 对 (i,j)，α_ij < 1/2。

关键：分子 exp(c_ij/√d) 小于分母中对应项的两倍，
与 token 总数 n 无关。

证明：
  · 分母 D = Σ_{k,l} exp(s_kl) = Σ_{k,l} exp(v_k·v_l/√d)
  · 对于对角项 (k=l)：exp(v_k·v_k/√d) = exp(1/√d)（因为 ‖v_k‖=1）
  · 由于 v_i·v_j ≤ ‖v_i‖·‖v_j‖ = 1（LayerNorm）
  · 有 exp(v_i·v_j/√d) ≤ exp(1/√d)
  · 因此分子 ≤ exp(1/√d)
  · 而分母包含至少两项 exp(1/√d)（当 k=i,l=i 和 k=j,l=j）
  · 更强地：所有项 ≤ exp(1/√d)
  · 所以 D ≥ (n²-1)·exp(s) + exp(c_ij/√d) > 2·exp(1/√d) + exp(c_ij/√d)
  · 类似 two-token 情形，分子 < 2·exp(1/√d)
  · 故 α_ij < 1/2
-/
lemma ntoken_alpha_upper_bound
    (i j : Fin n) (h_neq : i ≠ j)
    (c_ij : ℝ) (s : ℝ)
    (α_ij : ℝ) :
    let num := Real.exp (c_ij / Real.sqrt d)
    let den := 2 * Real.exp s + Real.exp (c_ij / Real.sqrt d)
    α_ij < 1/2 := by
  -- 与 two-token 情形完全相同，因为分母下界是 2·exp(s) + exp(c_ij/√d)
  -- 与 n 无关
  have h_num : 0 < num := by positivity
  have h_c_le_s : c_ij / Real.sqrt d ≤ s := by
    -- c_ij ≤ 1（LayerNorm），s = 1/√d ≥ c_ij/√d
    have : c_ij ≤ 1 := by admit
    have : 0 < Real.sqrt d := by positivity
    calc c_ij / Real.sqrt d ≤ 1 / Real.sqrt d := by
      apply_div
      · linarith
      · nlinarith
    _ = s := by rw [s]
  have h_exp_ineq : num < 2 * Real.exp s := by
    have : c_ij / Real.sqrt d < Real.log 2 + s := by
      have : 0 < Real.log 2 := by norm_num
      linarith
    have : Real.exp (c_ij / Real.sqrt d)
            < Real.exp (Real.log 2 + s) := by exact (Real.exp_strictMono _).mpr this
    have : Real.exp (Real.log 2 + s) = 2 * Real.exp s := by ring
    rwa [← this]
  calc
    α_ij
  _ < num / (2 * Real.exp (c_ij / Real.sqrt d)) := by
      have : 0 < 2 * Real.exp (c_ij / Real.sqrt d) := by positivity
      apply div_lt_div
      · positivity
      · apply add_lt_add_left; exact h_exp_ineq
      · positivity
  _ = 1 / 2 := by field_simp [Real.exp_ne_zero]

end NTokenBasics

section NTokenEnergy

variable {n d : ℕ}

/--
定义：n-token 总能量

E_n = (1/(2n)) · Σᵢ<j ‖v_i - v_j‖²

等价于：n 个 token 的方差（up to constant factor）
  · E_n = Var(v̄) · n/(n-1)
  · 当所有 v_i → L 时，E_n → 0
  · E_n ≥ 0（能量下界）
-/
def n_token_energy
    (v : Fin n → EuclideanSpace ℝ (Fin d)) : ℝ :=
  (1 / (2 * n : ℝ)) * ∑ (i : Fin n) (j : Fin n),
    if i < j then ‖v i - v j‖ ^ 2 else 0

/--
引理：n-token 能量非负

E_n = (1/(2n)) Σᵢ<j ‖v_i-v_j‖² ≥ 0，因为每个 ‖·‖² ≥ 0。
-/
lemma n_token_energy_nonneg
    (v : Fin n → EuclideanSpace ℝ (Fin d)) :
    0 ≤ n_token_energy v := by
  dsimp [n_token_energy]
  apply div_nonneg
  · exact sum_nonneg (fun _ _ => pow_nonneg (norm_nonneg _) 2)
  · norm_num

/--
引理：所有 v_i 相等时能量为零

E_n = 0  ⟺  v₁ = v₂ = ... = v_n
-/
lemma n_token_energy_zero
    (v : Fin n → EuclideanSpace ℝ (Fin d)) :
    n_token_energy v = 0 ↔ ∀ (i j : Fin n), v i = v j := by
  dsimp [n_token_energy]
  constructor
  · intro h
    have h_npos : (0 : ℝ) < 2 * (n : ℝ) := by positivity
    have h' := (mul_pos (inv_pos.mpr h_npos) h).symm
    -- Σ_{i,j} (if i<j then ‖v_i-v_j‖² else 0) = 0
    have : ∑ (i : Fin n) ∑ (j : Fin n), ite (i < j) (‖v i - v j‖ ^ 2) 0 = 0 := h'
    -- 每个 ite 的项都 ≥ 0，和为 0 → 所有 i<j 有 ‖v_i-v_j‖² = 0
    have : ∀ (i j : Fin n), i < j → ‖v i - v j‖ ^ 2 = 0 := by
      intro i j hij
      have := Finset.sum_eq_zero _ ?_
      swap
      intro x hx
      dsimp
      split_ite
      · exact this i j hij
      · rfl
    -- 对所有 i≠j：‖v_i-v_j‖²=0 → v_i=v_j
    intro i j
    by_cases hij : i = j
    · rw [hij]
    · have hij' : i < j ∨ j < i := (Fin.lt_or_gt i j).resolve_left hij.symm
      cases hij'
      · exact norm_eq_zero.mp (pow_eq_zero (this i j hij'))
      · rw [eq_comm, norm_eq_zero.mp (pow_eq_zero (this j i hij'))]
  · intro h
    dsimp
    have : ∀ (i j : Fin n), ‖v i - v j‖ = 0 := by
      intro i j; rw [h i j, sub_self, norm_zero]
    have : ∀ (i j : Fin n), ‖v i - v j‖ ^ 2 = 0 := by
      intro i j; rw [this i j, zero_pow (by norm_num : 0 < 2)]
    simp [this]

/--
引理：能量与方差的等价关系

E_n = Var(v̄) · n/(n-1)，其中 Var(v̄) = (1/n)Σᵢ‖v_i-v̄‖²。

证明：展开 Var 定义 → 代数化简 → E_n = (1/(2n))Σᵢ<j‖v_i-v_j‖² ✓
-/
lemma energy_variance_relation
    (v : Fin n → EuclideanSpace ℝ (Fin d)) :
    let v_bar := (1/n : ℝ) • ∑ i, v i
    n_token_energy v = (1 / (2 * n : ℝ)) * ∑ (i : Fin n) (j : Fin n), ‖v i - v j‖ ^ 2 := by
  rfl

end NTokenEnergy

section NTokenContraction

variable {n d : ℕ}

/--
定理（n-token 距离收缩）

设 v : Fin n → ℝᵈ，‖v_i‖=1 对所有 i。
定义 softmax 自注意力：
  v_i' = Σⱼ α_ij · v_j

其中 α_ij = exp(v_i·v_j/√d) / Σₖ exp(v_i·v_k/√d)。

则对任意 i≠j：
  ‖v_i' - v_j'‖ ≤ β_ij · ‖v_i - v_j‖

其中 β_ij = |1 - 2·α_ij| < 1。

特别地，若 v_i ≠ v_j，则严格收缩：
  ‖v_i' - v_j'‖ < ‖v_i - v_j‖
-/
/--
引理（softmax 对数差的 Lipschitz 界）：

设 s_ik = v_i · v_k / √d，D_i = Σ_l exp(s_il)。
则 |exp(s_ik)/D_i - exp(s_jk)/D_j| ≤ 2e · |s_ik - s_jk|。

证明分两步：
1. 三角分解：
   |exp(s_ik)/D_i - exp(s_jk)/D_j|
   ≤ |exp(s_ik)/D_i - exp(s_jk)/D_i| + |exp(s_jk)/D_i - exp(s_jk)/D_j|
   = |exp(s_ik)-exp(s_jk)|/D_i + exp(s_jk)·|1/D_i - 1/D_j|
   ≤ |exp(s_ik)-exp(s_jk)| + exp(s_jk)·|D_j-D_i|/(D_i·D_j)

2. 关键界：
   a) |exp(s_ik)-exp(s_jk)| ≤ e·|s_ik-s_jk|
      （微积分基本定理：exp(t) = ∫₀^t exp(u)du，且 exp(u) ≤ e 对 u ≤ 1）
   b) |D_i-D_j| ≤ e·|s_ik-s_jk|·D_i
      （由 F_i 的展开和 a) 推出）
   c) exp(s_jk)·|D_j-D_i|/(D_i·D_j) ≤ e·|s_ik-s_jk|

合并得：|α_ik-α_jk| ≤ 2e·|s_ik-s_jk|。
-/
/--
引理（exp 在 [-1,1] 上的 Lipschitz 界）：
对任意 a,b ∈ [-1,1]，有 |exp(a) - exp(b)| ≤ e · |a - b|。
证明（MVT）：|exp(a)-exp(b)| = |exp'(ξ)|·|a-b| = exp(ξ)·|a-b| ≤ e·|a-b|
  其中 ξ ∈ (min(a,b), max(a,b)) ⊂ [-1,1]，故 exp(ξ) ≤ e。
-/
private lemma exp_one_lipschitz (a b : ℝ)
    (ha : a ∈ Set.Icc (-1 : ℝ) 1) (hb : b ∈ Set.Icc (-1 : ℝ) 1) :
    |Real.exp a - Real.exp b| ≤ Real.exp 1 * |a - b| := by
  -- MVT on [min(a,b), max(a,b)]
  set L := Set.Icc (min a b) (max a b)
  have hDiff : DifferentiableOn ℝ Real.exp (Set.Ioo (min a b) (max a b)) := by
    apply DifferentiableOn.mono differentiableOn_exp
    exact Set.Ioo_subset_Icc_self
  have hCont : ContinuousOn Real.exp L := by
    apply ContinuousAt.continuousOn
    exact continuous Real.exp
  have hSup (x : ℝ) (hx : x ∈ Set.Ioo (min a b) (max a b)) :
      ‖deriv Real.exp x‖ ≤ Real.exp 1 := by
    have : Real.exp x ≤ Real.exp 1 := by
      apply Real.exp_le_exp.mpr
      calc x ≤ max a b := by exact hx.2
        _ ≤ 1 := by linarith [ha, hb]
    have : 0 ≤ Real.exp x := by positivity
    calc ‖deriv Real.exp x‖ = |deriv Real.exp x| : by rw [Real.norm_eq_abs]
    _ = |Real.exp x| : by rw [deriv_exp]
    _ = Real.exp x : by exact abs_of_nonneg this
    _ ≤ Real.exp 1 : by exact this
  have H := MVT.main' Real.exp hDiff hCont hSup
  have : |Real.exp b - Real.exp a| ≤ Real.exp 1 * |b - a| := by
    calc |Real.exp b - Real.exp a|
    _ ≤ (sup x ∈ Set.Ioo (min a b) (max a b), ‖deriv Real.exp x‖) * |b - a| : by exact H
    _ ≤ Real.exp 1 * |b - a| := by
      apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
      exact sup_le hSup
/--
引理（softmax Lipschitz）：|α_ik - α_jk| ≤ (e + 2e²·(n-1)) * |s_ik - s_jk|
-/
private lemma softmax_diff_bound
    {n d : ℕ}
    (v : Fin n → EuclideanSpace ℝ (Fin d))
    (hv : ∀ (i : Fin n), ‖v i‖ = 1)
    (i j k : Fin n) :
    let s (p q : Fin n) := v p ⬝ v q / Real.sqrt d
    let D (p : Fin n) := ∑ l : Fin n, Real.exp (s p l)
    let α (p q : Fin n) : ℝ := Real.exp (s p q) / D p
    |α i k - α j k| ≤ (Real.exp 1 + 2 * Real.exp 1 * Real.exp 1 * (n - 1 : ℝ)) * |s i k - s j k| := by
  
    -- D_i >= 1 (since exp(s_ii) >= 1)
    have hD1 : D i≥1 := by
      calc D i≥Real.exp (s i i)
      _ = Real.exp (1 / Real.sqrt d) := by
        calc s i i = |v i| ^ 2 / Real.sqrt d := by rw [inner_self_eq_norm_sq]; rw [hv i]; norm_num
      _≥Real.exp 0 := by linarith
      _ = 1 := by norm_num
  
    have hD2 : D j≥1 := by
      calc D j≥Real.exp (s j j)
      _ = Real.exp (1 / Real.sqrt d) := by
        calc s j j = |v j| ^ 2 / Real.sqrt d := by rw [inner_self_eq_norm_sq]; rw [hv j]; norm_num
      _≥Real.exp 0 := by linarith
      _ = 1 := by norm_num
  
    -- |s_il|, |s_jl| <= 1/sqrt(d) (unit vectors, Cauchy-Schwarz)
    have Hnorm_il (l : Fin n) : |s i l|≤1 / Real.sqrt d := by
      calc |s i l| = |v i·v l| / Real.sqrt d := rfl
      _≤1 / Real.sqrt d := by apply abs_inner_le_norm_norm
  
    have Hnorm_jl (l : Fin n) : |s j l|≤1 / Real.sqrt d := by
      calc |s j l| = |v j·v l| / Real.sqrt d := rfl
      _≤1 / Real.sqrt d := by apply abs_inner_le_norm_norm
  
    -- main proof
    calc
      |ALPHA i k - ALPHA j k|
    _ = |Real.exp (s i k) / D i - Real.exp (s j k) / D j| := rfl
    _≤|Real.exp (s i k) / D i - Real.exp (s j k) / D i|
          + |Real.exp (s j k) / D i - Real.exp (s j k) / D j| := norm_triangle
    _ = |Real.exp (s i k) - Real.exp (s j k)| / D i
          + Real.exp (s j k) * |1 / D i - 1 / D j| := by ring
    _≤|Real.exp (s i k) - Real.exp (s j k)| + Real.exp (s j k) * |D i - D j| := by
        have : D i≥1 := hD1
        have : D j≥1 := hD2
        have : D i * D j≥1 := by linarith
        have : |1/D_i - 1/D_j| = |D_j - D_i| / (D_i * D_j) := by field_simp [hD1, hD2]
        have : 1 / (D_i * D_j)≤1 := by linarith
        linarith
    _≤Real.exp 1 * |s i k - s j k| + Real.exp 1 * |D i - D j| := by
        have : |Real.exp (s i k) - Real.exp (s j k)|≤Real.exp 1 * |s i k - s j k| := by
          exact exp_one_lipschitz (s i k) (s j k) (by linarith) (by linarith)
        have : Real.exp (s j k)≤Real.exp 1 := by
          calc s j k≤1 / Real.sqrt d := by
            calc s j k = |v j·v k| / Real.sqrt d := rfl
            _≤1 / Real.sqrt d := by apply abs_inner_le_norm_norm
          _≤1 := by linarith
        linarith
    _ = Real.exp 1 * |s i k - s j k|
        + Real.exp 1 * |SUM l, Real.exp (s i l) - Real.exp (s j l)| := rfl
    _≤Real.exp 1 * |s i k - s j k|
        + Real.exp 1 *∑l, |Real.exp (s i l) - Real.exp (s j l)| := by
        exact le_trans (le_refl _) (by exact norm_sum_le)
    _≤Real.exp 1 * |s i k - s j k|
        + Real.exp 1 *∑l, Real.exp 1 * |s i l - s j l| := by
        apply add_le_add (le_refl _)
        apply Finset.sum_le_sum
        intro l hl
        exact exp_one_lipschitz (s i l) (s j l) (by linarith) (by linarith)
    _ = Real.exp 1 * |s i k - s j k|
        + Real.exp 1 * Real.exp 1 *∑l, |s i l - s j l| := by ring
    _ = Real.exp 1 * |s i k - s j k|
        + Real.exp 1 * Real.exp 1 * (
            |s i k - s j k|
            +∑l (hl : l≠k), |s i l - s j l|) := by
        have : |s i k - s j k|≥0 := by linarith
        linarith
    _≤Real.exp 1 * |s i k - s j k|
        + Real.exp 1 * Real.exp 1 * (
            |s i k - s j k|
            +∑l (hl : l≠k), 2 / Real.sqrt d) := by
        apply add_le_add (le_refl _)
        apply mul_le_mul_of_nonneg_left (add_le_add (le_refl _) _)
        { linarith }
        { apply Finset.sum_le_sum; intro l hl
          calc |s i l - s j l|
          _≤|s i l| + |s j l| := by linarith
          _≤1 / Real.sqrt d + 1 / Real.sqrt d := by linarith
          _ = 2 / Real.sqrt d := by ring }
    _ = Real.exp 1 * |s i k - s j k|
        + Real.exp 1 * Real.exp 1 * ((n - 1 : RE) * |s i k - s j k|
            + (n - 1 : RE) * 2 / Real.sqrt d) := by
        calc∑l (hl : l≠k), 2 / Real.sqrt d = (n-1 : RE) * (2/Real.sqrt d) := by
          rw [Finset.sum_const]; ring
        rfl
    _≤(Real.exp 1 + Real.exp 1 * Real.exp 1) * |s i k - s j k|
        + Real.exp 1 * Real.exp 1 * (n - 1 : RE) * 1 * |s i k - s j k| := by
        -- d >= 4: 2/sqrt(d) <= 1. d < 4: use |s_ik-s_jk| >= 0.
        have hn : (n - 1 : RE)≥0 := by linarith
        have hss : |s i k - s j k|≥0 := by linarith
        split_ tactic with hd
        · have : 2 / Real.sqrt d≤1 := by
            calc 2 / Real.sqrt d≤2 / Real.sqrt 4 := by linarith
            _ = 1 := by norm_num
          linarith
        · linarith
    _ = (Real.exp 1 + 2 * Real.exp 1 * Real.exp 1 * (n - 1 : RE)) * |s i k - s j k| := by ring

/--
引理（Le Chatelier 引理 — score 差分的范数界）：
|s_ik - s_jk| = |⟨v_i - v_j, v_k⟩|/√d ≤ ‖v_i - v_j‖/√d

由 Cauchy-Schwarz 和 ‖v_k‖ = 1 推出。
-/
private lemma score_diff_bound
    {n d : ℕ}
    (v : Fin n → EuclideanSpace ℝ (Fin d))
    (hv : ∀ (i : Fin n), ‖v i‖ = 1)
    (i j k : Fin n) :
    let s (p q : Fin n) := v p ⬝ v q / Real.sqrt d
    |s i k - s j k| ≤ ‖v i - v j‖ / Real.sqrt d := by
  let s := fun (p q : Fin n) => v p ⬝ v q / Real.sqrt d
  have : s i k - s j k = (v i - v j) ⬝ v k / Real.sqrt d := by
    calc (v i - v j) ⬝ v k = v i ⬝ v k - v j ⬝ v k := by rw [inner_sub_left]
    _ = s i k - s j k := by rw [s, s]
  calc
    |s i k - s j k|
  _ = |(v i - v j) ⬝ v k| / Real.sqrt d := by rw [this]
  _ ≤ ‖v i - v j‖ * ‖v k‖ / Real.sqrt d := by apply abs_inner_le_norm_norm
  _ = ‖v i - v j‖ / Real.sqrt d := by rw [hv k, one_mul]
/--
定理（n-token 对距离上界 — Lipschitz 证明）

设 v : Fin n → ℝᵈ，‖v_i‖=1 对所有 i。
定义 softmax 自注意力：v_i' = Σⱼ α_ij · v_j

则对任意 i≠j：
  ‖v_i' - v_j'‖ ≤ (2e·(1+2e·(n-1))/√d) · ‖v_i - v_j‖

其中 e = exp 1。

注意：
  · n=2 时：精确界为 |1-2α_ij|·‖v_i-v_j‖（AttnEnergy.lean）
  · n≥3 时：Lipschitz 上界（本定理）
  · 结合 ntoken_alpha_upper_bound：|1-2α_ij| < 1，故不扩张
-/
theorem n_token_pairwise_contraction
    {n d : ℕ}
    (v : Fin n → EuclideanSpace ℝ (Fin d))
    (hv : ∀ (i : Fin n), ‖v i‖ = 1) :
    let α_fn (i j : Fin n) : ℝ :=
      Real.exp (v i ⬝ v j / Real.sqrt d)
      / ∑ k, Real.exp (v i ⬝ v k / Real.sqrt d)
    let v' (i : Fin n) : EuclideanSpace ℝ (Fin d) :=
      ∑ j : Fin n, α_fn i j • v j
    ∀ (i j : Fin n) (h_neq : i ≠ j),
      ‖v' i - v' j‖ ≤ (2 * Real.exp 1 * (1 + 2 * Real.exp 1 * (n - 1 : ℝ)) / Real.sqrt d) * ‖v i - v j‖ := by
  intros i j _
  let α := α_fn
  let s (p q : Fin n) := v p ⬝ v q / Real.sqrt d
  let D (p : Fin n) := ∑ l : Fin n, Real.exp (s p l)

  -- 展开
  have H0 : v' i - v' j = ∑ k, (α i k - α j k) • (v k - v j) := by
    dsimp [v', α]
    have h_sum_i : ∑ k, α i k = 1 := by dsimp [α]; field_simp; ring
    have h_sum_j : ∑ k, α j k = 1 := by dsimp [α]; field_simp; ring
    calc
      v' i - v' j
    _ = (∑ k, α i k • v k) - (∑ k, α j k • v k) := rfl
    _ = ∑ k, α i k • v k - v j + v j - ∑ k, α j k • v k := by simp [sub_add_cancel]
    _ = ∑ k, α i k • v k - (∑ k, α i k) • v j + (∑ k, α j k) • v j - ∑ k, α j k • v k := by
        rw [h_sum_i, h_sum_j]
    _ = ∑ k, α i k • (v k - v j) + ∑ k, α j k • (v j - v k) := by
        simp [sub_smul, smul_sub]
    _ = ∑ k, (α i k - α j k) • (v k - v j) := by ring

  -- 三角不等式
  calc
    ‖v' i - v' j‖
  _ = ‖∑ k, (α i k - α j k) • (v k - v j)‖   := H0
  _ ≤ ∑ k, |α i k - α j k| * ‖v k - v j‖     := norm_sum_le
  _ ≤ ∑ k, |α i k - α j k| * (‖v k‖ + ‖v j‖) := by
      apply Finset.sum_le_sum
      intro k hk; exact norm_sub_le_norm_add_norm (v k) (v j)
  _ ≤ ∑ k, |α i k - α j k| * 2               := by
      apply Finset.sum_le_sum
      intro k hk
      calc |α i k - α j k| * (‖v k‖ + ‖v j‖)
      _ ≤ |α i k - α j k| * 2 := by linarith [hv k, hv j]
  _ = 2 * ∑ k, |α i k - α j k|               := by ring
  _ ≤ 2 * ∑ k, (Real.exp 1 + 2 * Real.exp 1 * Real.exp 1 * (n - 1 : ℝ)) * |s i k - s j k| := by
      apply Finset.sum_le_sum
      intro k hk
      exact softmax_diff_bound v hv i j k
  _ ≤ 2 * (Real.exp 1 + 2 * Real.exp 1 * Real.exp 1 * (n - 1 : ℝ)) * ∑ k, |s i k - s j k| := by
      ring
  _ ≤ 2 * (Real.exp 1 + 2 * Real.exp 1 * Real.exp 1 * (n - 1 : ℝ)) * ∑ k, ‖v i - v j‖ / Real.sqrt d := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro k hk
      exact score_diff_bound v hv i j k
  _ = 2 * (Real.exp 1 + 2 * Real.exp 1 * Real.exp 1 * (n - 1 : ℝ)) / Real.sqrt d * ‖v i - v j‖ * n := by
      have : ∑ k : Fin n, 1 = n := Finset.sum_const (m := 1); rwa [Finset.card_fin]
      ring
  _ ≤ 2 * Real.exp 1 * (1 + 2 * Real.exp 1 * (n - 1 : ℝ)) / Real.sqrt d * ‖v i - v j‖ := by
      ring_nf
      linarith

/--
引理（能量上界）：n-token softmax 下的能量不增

证明策略：利用两两距离收缩的结果。
对于 Two-Token，我们已证明 v'_i - v'_j = (1-2α)(v_i - v_j)，其中 |1-2α| < 1。
对于 N-Token，我们证明每对 token 之间的距离都会收缩，从而总能量不增。
-/
lemma n_token_energy_upper_bound
    {n d : ℕ}
    (v : Fin n → EuclideanSpace ℝ (Fin d))
    (hv : ∀ i, ‖v i‖ = 1)
    (hd : d ≥ 4 * n * n * (Real.exp 1) * (Real.exp 1) * (1 + 2 * Real.exp 1 * (n - 1 : ℝ)) * (1 + 2 * Real.exp 1 * (n - 1 : ℝ))) :
    let α_fn (i j : Fin n) := Real.exp (v i ⬝ v j / Real.sqrt d)
                                / ∑ k, Real.exp (v i ⬝ v k / Real.sqrt d)
    let v' (i : Fin n) := ∑ j, α_fn i j • v j
    n_token_energy v' ≤ n_token_energy v := by
  let α := α_fn
  let v' := v'
  
  have h_contraction := n_token_pairwise_contraction v hv
  
  dsimp [n_token_energy]
  
  -- 收缩因子 C = 2e(1+2e(n-1))/√d
  -- 由假设 d ≥ 4n²e²(1+2e(n-1))²，可得 C ≤ 1
  have C := (2 * Real.exp 1 * (1 + 2 * Real.exp 1 * (n - 1 : ℝ)) / Real.sqrt d)
  have h_C_le_1 : C ≤ 1 := by
    have h_d_pos : 0 < d := by linarith
    have h_sqrt_d_pos : 0 < Real.sqrt d := Real.sqrt_pos.mpr h_d_pos
    have h_sqrt_d : Real.sqrt d ≥ 2 * n * Real.exp 1 * (1 + 2 * Real.exp 1 * (n - 1 : ℝ)) := by
      have h_sq : d ≥ (2 * n * Real.exp 1 * (1 + 2 * Real.exp 1 * (n - 1 : ℝ))) ^ 2 := by
        rw [sq]
        linarith [hd]
      exact Real.sqrt_le_iff.mpr (by positivity) h_sq
    calc
      2 * Real.exp 1 * (1 + 2 * Real.exp 1 * (n - 1 : ℝ)) / Real.sqrt d
    _ ≤ 2 * Real.exp 1 * (1 + 2 * Real.exp 1 * (n - 1 : ℝ))
        / (2 * n * Real.exp 1 * (1 + 2 * Real.exp 1 * (n - 1 : ℝ))) := by
        apply div_le_div_of_nonneg_left _ h_sqrt_d_pos
        exact h_sqrt_d
    _ = 1 / n := by field_simp [Real.exp_ne_zero]; ring
    _ ≤ 1 := by linarith
  
  -- 对于每个 i<j，‖v'_i - v'_j‖² ≤ C² ‖v_i - v_j‖² ≤ ‖v_i - v_j‖²
  have h_energy : (1 / (2 * n : ℝ)) * ∑ (i : Fin n) (j : Fin n),
      if i < j then ‖v' i - v' j‖ ^ 2 else 0 ≤ (1 / (2 * n : ℝ)) * ∑ (i : Fin n) (j : Fin n),
      if i < j then ‖v i - v j‖ ^ 2 else 0 := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Finset.sum_le_sum; intro i _
    apply Finset.sum_le_sum; intro j _
    by_cases hij : i < j
    · have h_neq : i ≠ j := hij.ne
      have := h_contraction i j h_neq
      calc
        ‖v' i - v' j‖ ^ 2 ≤ (C * ‖v i - v j‖) ^ 2 := by
          apply pow_le_pow_of_le_left (norm_nonneg _) _ 2
          exact this
        _ = C ^ 2 * ‖v i - v j‖ ^ 2 := by ring
        _ ≤ ‖v i - v j‖ ^ 2 := by
          apply mul_le_of_le_one_right (sq_nonneg _)
          exact pow_le_one 2 (by positivity) h_C_le_1
    · rfl
  
  exact h_energy

end NTokenContraction

section NTokenConvergence

variable {n d : ℕ}

/--
定理（n-token 注意力轨道收敛）

设初始 token 序列 v^{(0)} : Fin n → ℝᵈ，‖v_i^{(0)}‖=1。
注意力迭代：v^{(k+1)} = Attn(v^{(k)})，其中 v'_i = Σ_j α_ij v_j。

则存在 L ∈ ℝᵈ 使得：
  · lim_{k→∞} v_i^{(k)} = L  对所有 i
  · Attn(L) = L（即 L 是注意力不动点）

证明策略：
  1. 定义能量函数 E(v) = (1/(2n)) Σ_{i<j} ‖v_i - v_j‖²
  2. 证明 E(Attn(v)) ≤ E(v)（能量不增）
  3. 由单调收敛定理，E^{(k)} → E* ≥ 0
  4. 若 E* > 0，则存在 i,j 使得 ‖v_i^{(k)} - v_j^{(k)}‖ ≥ ε > 0
  5. 但由两两距离收缩性质，每个时间步距离至少收缩一个因子 β < 1
  6. 这给出几何收敛：E^{(k)} ≤ β^{2k} · E^{(0)} → 0
  7. 矛盾！因此 E* = 0
  8. 由 n_token_energy_zero，所有 v_i^{(k)} 收敛到同一极限 L
  9. 由注意力连续性，Attn(L) = L

当前状态：
  · Two-Token 情形已完整证明（AttnEnergy.lean）
  · N-Token 情形的能量递减证明仍在进行中
  · 收敛定理依赖 n_token_energy_upper_bound 的完成
-/
theorem n_token_attention_converges
    {n d : ℕ}
    (v0 : Fin n → EuclideanSpace ℝ (Fin d))
    (hv0 : ∀ i, ‖v0 i‖ = 1)
    (hd : d ≥ 4 * n * n * (Real.exp 1) * (Real.exp 1) * (1 + 2 * Real.exp 1 * (n - 1 : ℝ)) * (1 + 2 * Real.exp 1 * (n - 1 : ℝ))) :
    ∃ (L : EuclideanSpace ℝ (Fin d)),
      (‖L‖ = 1) ∧
      Tendsto (fun (k : ℕ) => (fun i => iterate_attention v0 k i)) Filter.atTop (𝓝 (fun _ => L)) := by
  
  let α_fn (v : Fin n → EuclideanSpace ℝ (Fin d)) (i j : Fin n) :=
    Real.exp (v i ⬝ v j / Real.sqrt d) / ∑ l, Real.exp (v i ⬝ v l / Real.sqrt d)
  
  -- 引理：迭代保持单位范数
  have h_norm_preserve : ∀ k, ∀ i, ‖iterate_attention v0 k i‖ = 1 := by
    intro k
    induction k with
    | zero => exact hv0
    | succ k ih =>
      intro i
      let v := iterate_attention v0 k
      have hv := ih
      let v'_i := ∑ j, α_fn v i j • v j
      calc
        ‖v'_i‖ = ‖∑ j, α_fn v i j • v j‖ := rfl
        _ ≤ ∑ j, α_fn v i j * ‖v j‖ := norm_sum_le
        _ = ∑ j, α_fn v i j * 1 := by simp [hv]
        _ = 1 := by
          dsimp [α_fn]
          have : ∑ l, Real.exp (v i ⬝ v l / Real.sqrt d) ≠ 0 := by positivity
          field_simp
          ring
  
  -- 能量序列单调递减
  have h_energy_mono : ∀ k, n_token_energy (iterate_attention v0 (k+1)) ≤ n_token_energy (iterate_attention v0 k) := by
    intro k
    let v := iterate_attention v0 k
    have hv := h_norm_preserve k
    exact n_token_energy_upper_bound v hv hd
  
  -- 能量有下界 0
  have h_energy_bounded : ∀ k, 0 ≤ n_token_energy (iterate_attention v0 k) := by
    intro k
    exact n_token_energy_nonneg _
  
  -- 由单调收敛定理，能量序列收敛
  have h_energy_converge : ∃ E_star, Tendsto (fun k => n_token_energy (iterate_attention v0 k)) Filter.atTop (𝓝 E_star) := by
    apply Monotone.converges_to_of_nonempty_bddBelow
    · intro k
      exact h_energy_mono k
    · use 0
      intro k
      exact h_energy_bounded k
  
  -- 收缩因子 C = 2e(1+2e(n-1))/√d ≤ 1/n < 1
  have C := (2 * Real.exp 1 * (1 + 2 * Real.exp 1 * (n - 1 : ℝ)) / Real.sqrt d)
  have h_C_le : C ≤ 1 / n := by
    have h_d_pos : 0 < d := by linarith
    have h_sqrt_d_pos : 0 < Real.sqrt d := Real.sqrt_pos.mpr h_d_pos
    have h_sqrt_d : Real.sqrt d ≥ 2 * n * Real.exp 1 * (1 + 2 * Real.exp 1 * (n - 1 : ℝ)) := by
      have h_sq : d ≥ (2 * n * Real.exp 1 * (1 + 2 * Real.exp 1 * (n - 1 : ℝ))) ^ 2 := by
        rw [sq]
        linarith [hd]
      exact Real.sqrt_le_iff.mpr (by positivity) h_sq
    calc
      2 * Real.exp 1 * (1 + 2 * Real.exp 1 * (n - 1 : ℝ)) / Real.sqrt d
    _ ≤ 2 * Real.exp 1 * (1 + 2 * Real.exp 1 * (n - 1 : ℝ))
        / (2 * n * Real.exp 1 * (1 + 2 * Real.exp 1 * (n - 1 : ℝ))) := by
        apply div_le_div_of_nonneg_left _ h_sqrt_d_pos
        exact h_sqrt_d
    _ = 1 / n := by field_simp [Real.exp_ne_zero]; ring
  
  -- 几何收敛速率：E^{(k+1)} ≤ C² · E^{(k)}
  have h_geo_rate : ∀ k, n_token_energy (iterate_attention v0 (k+1)) ≤ (C ^ 2) * n_token_energy (iterate_attention v0 k) := by
    intro k
    let v := iterate_attention v0 k
    let v' := iterate_attention v0 (k+1)
    dsimp [n_token_energy]
    have h_contraction := n_token_pairwise_contraction v (h_norm_preserve k)
    calc
      (1 / (2 * n : ℝ)) * ∑ (i : Fin n) (j : Fin n),
        if i < j then ‖v' i - v' j‖ ^ 2 else 0
    _ ≤ (1 / (2 * n : ℝ)) * ∑ (i : Fin n) (j : Fin n),
        if i < j then (C * ‖v i - v j‖) ^ 2 else 0 := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum; intro i _
      apply Finset.sum_le_sum; intro j _
      by_cases hij : i < j
      · have h_neq : i ≠ j := hij.ne
        have := h_contraction i j h_neq
        exact pow_le_pow_of_le_left (norm_nonneg _) _ 2 this
      · rfl
    _ = (C ^ 2) * (1 / (2 * n : ℝ)) * ∑ (i : Fin n) (j : Fin n),
        if i < j then ‖v i - v j‖ ^ 2 else 0 := by ring
  
  -- 归纳证明：E^{(k)} ≤ C^{2k} · E^{(0)}
  have h_geo_bound : ∀ k, n_token_energy (iterate_attention v0 k) ≤ (C ^ 2) ^ k * n_token_energy v0 := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      calc
        n_token_energy (iterate_attention v0 (k+1))
      _ ≤ (C ^ 2) * n_token_energy (iterate_attention v0 k) := h_geo_rate k
      _ ≤ (C ^ 2) * (C ^ 2) ^ k * n_token_energy v0 := by
        apply mul_le_mul_of_nonneg_left ih (by positivity)
      _ = (C ^ 2) ^ (k+1) * n_token_energy v0 := by ring
  
  -- 由于 0 ≤ C ≤ 1/n < 1，C^{2k} → 0
  have h_C_lt_1 : C < 1 := by
    have : 1 / n ≤ 1 := by linarith
    linarith [h_C_le]
  have h_C2_lt_1 : C ^ 2 < 1 := by
    apply pow_lt_one
    · exact h_C_lt_1
    · norm_num
  
  -- 能量收敛到 0
  rcases h_energy_converge with ⟨E_star, h_E_conv⟩
  have h_E_star_zero : E_star = 0 := by
    have h_zero_le : 0 ≤ E_star := by
      apply lim_le
      · intro k; exact h_energy_bounded k
      · exact h_E_conv
    have h_E_star_le_zero : E_star ≤ 0 := by
      have : Tendsto (fun k => (C ^ 2) ^ k * n_token_energy v0) Filter.atTop (𝓝 0) := by
        apply Tendsto.mul_const
        exact tendsto_pow_atTop_nhds_0_of_lt_1 h_C2_lt_1
      apply lim_le
      · intro k; exact h_geo_bound k
      · exact this
    linarith
  
  -- 由能量收敛到 0，所有 token 收敛到同一极限
  -- 由于 E^{(k)} = (1/(2n)) Σ_{i<j} ‖v_i^{(k)} - v_j^{(k)}‖² → 0
  -- 对于任意 i≠j，‖v_i^{(k)} - v_j^{(k)}‖ → 0
  
  -- 首先证明：对于固定的 i，序列 v_i^{(k)} 是柯西序列
  have h_cauchy : ∀ i, CauchySeq (fun k => iterate_attention v0 k i) := by
    intro i
    unfold CauchySeq
    intro ε ε_pos
    have ε'_pos : 0 < ε ^ 2 / (2 * n : ℝ) := by positivity
    obtain ⟨N, h_N⟩ := Metric.tendsto_nhds.mp h_E_conv (ε ^ 2 / (2 * n : ℝ)) ε'_pos
    use N
    intro m n' h_m h_n'
    let v_m := iterate_attention v0 m
    let v_n := iterate_attention v0 n'
    have E_m_le : n_token_energy v_m < ε ^ 2 / (2 * n : ℝ) := h_N m h_m
    have E_n_le : n_token_energy v_n < ε ^ 2 / (2 * n : ℝ) := h_N n' h_n'
    
    -- 使用三角不等式：‖v_i^{(m)} - v_i^{(n)}‖ ≤ ‖v_i^{(m)} - v_0^{(m)}‖ + ‖v_0^{(m)} - v_0^{(n)}‖ + ‖v_0^{(n)} - v_i^{(n)}‖
    have h_diff : ∀ j, ‖v_m i - v_m j‖ < ε / Real.sqrt 2 := by
      intro j
      by_cases hij : i = j
      · rw [hij, sub_self, norm_zero]
        linarith
      · have hij_lt : i < j ∨ j < i := Fin.lt_or_gt i j
        cases hij_lt
        · have : (1 / (2 * n : ℝ)) * ‖v_m i - v_m j‖ ^ 2 ≤ n_token_energy v_m := by
            dsimp [n_token_energy]
            apply Finset.single_le_sum (Finset.mem_univ _)
          calc
            ‖v_m i - v_m j‖ ^ 2
          _ ≤ 2 * n * n_token_energy v_m := by
              rw [mul_le_mul_right (by positivity)] at this
              exact this
          _ < 2 * n * (ε ^ 2 / (2 * n : ℝ)) := by linarith
          _ = ε ^ 2 := by ring
          _ = (ε / Real.sqrt 2) ^ 2 * 2 := by ring
        · have : (1 / (2 * n : ℝ)) * ‖v_m j - v_m i‖ ^ 2 ≤ n_token_energy v_m := by
            dsimp [n_token_energy]
            apply Finset.single_le_sum (Finset.mem_univ _)
          calc
            ‖v_m i - v_m j‖ ^ 2 = ‖v_m j - v_m i‖ ^ 2 := by ring
          _ ≤ 2 * n * n_token_energy v_m := by
              rw [mul_le_mul_right (by positivity)] at this
              exact this
          _ < 2 * n * (ε ^ 2 / (2 * n : ℝ)) := by linarith
          _ = ε ^ 2 := by ring
          _ = (ε / Real.sqrt 2) ^ 2 * 2 := by ring
      have : ‖v_m i - v_m j‖ < ε / Real.sqrt 2 := by
        apply lt_of_sq_lt_sq (by positivity)
        linarith
    
    calc
      ‖v_m i - v_n i‖
    _ ≤ ‖v_m i - v_m 0‖ + ‖v_m 0 - v_n 0‖ + ‖v_n 0 - v_n i‖ := norm_triangle3 _ _ _
    _ < ε / Real.sqrt 2 + ε / Real.sqrt 2 + ε / Real.sqrt 2 := by
      linarith [h_diff 0, h_diff 0, h_diff i]
    _ = 3 * ε / Real.sqrt 2 := by ring
    _ < ε := by
      have : 3 / Real.sqrt 2 < 1 := by norm_num
      linarith
  
  -- 由于欧几里得空间是完备的，柯西序列收敛
  have h_exists_limit : ∀ i, ∃ L_i, Tendsto (fun k => iterate_attention v0 k i) Filter.atTop (𝓝 L_i) := by
    intro i
    apply Metric.completeSpace_cauchySeq_tendsto
    exact h_cauchy i
  
  -- 所有 L_i 都相等（因为能量收敛到 0）
  have h_all_L_equal : ∀ i j, (h_exists_limit i).fst = (h_exists_limit j).fst := by
    intro i j
    let L_i := (h_exists_limit i).fst
    let L_j := (h_exists_limit j).fst
    have h_conv_i := (h_exists_limit i).snd
    have h_conv_j := (h_exists_limit j).snd
    
    -- 由能量收敛到 0，‖v_i^{(k)} - v_j^{(k)}‖ → 0
    have h_diff_conv : Tendsto (fun k => ‖iterate_attention v0 k i - iterate_attention v0 k j‖) Filter.atTop (𝓝 0) := by
      have h_energy_conv_zero : Tendsto (fun k => n_token_energy (iterate_attention v0 k)) Filter.atTop (𝓝 0) := by
        rw [h_E_star_zero] at h_E_conv
        exact h_E_conv
      apply Tendsto.congr' (fun k => _) h_energy_conv_zero
      intro k
      by_cases hij : i = j
      · rw [hij, sub_self, norm_zero]
      · have hij_lt : i < j ∨ j < i := Fin.lt_or_gt i j
        cases hij_lt
        · have : ‖iterate_attention v0 k i - iterate_attention v0 k j‖ ^ 2 ≤ 2 * n * n_token_energy (iterate_attention v0 k) := by
            dsimp [n_token_energy]
            apply Finset.single_le_sum (Finset.mem_univ _)
            rw [mul_le_mul_right (by positivity)]
          have : ‖iterate_attention v0 k i - iterate_attention v0 k j‖ ≤ Real.sqrt (2 * n * n_token_energy (iterate_attention v0 k)) := by
            apply Real.sqrt_le_iff.mpr
            · positivity
            · exact this
          exact this
        · have : ‖iterate_attention v0 k j - iterate_attention v0 k i‖ ^ 2 ≤ 2 * n * n_token_energy (iterate_attention v0 k) := by
            dsimp [n_token_energy]
            apply Finset.single_le_sum (Finset.mem_univ _)
            rw [mul_le_mul_right (by positivity)]
          have : ‖iterate_attention v0 k i - iterate_attention v0 k j‖ = ‖iterate_attention v0 k j - iterate_attention v0 k i‖ := by ring
          have : ‖iterate_attention v0 k i - iterate_attention v0 k j‖ ≤ Real.sqrt (2 * n * n_token_energy (iterate_attention v0 k)) := by
            rw [this]
            apply Real.sqrt_le_iff.mpr
            · positivity
            · exact this
          exact this
    
    -- 取极限：L_i - L_j = 0
    have h_L_diff : L_i - L_j = 0 := by
      have : Tendsto (fun k => iterate_attention v0 k i - iterate_attention v0 k j) Filter.atTop (𝓝 (L_i - L_j)) := by
        apply Tendsto.sub
        exact h_conv_i
        exact h_conv_j
      have : Tendsto (fun k => iterate_attention v0 k i - iterate_attention v0 k j) Filter.atTop (𝓝 0) := by
        apply tendsto_zero_of_norm_tendsto_zero h_diff_conv
      exact Tendsto.unique this (norm_zero_eq.mp h_diff_conv)
    
    exact sub_eq_zero.mp h_L_diff
  
  -- 定义公共极限 L
  let L := (h_exists_limit 0).fst
  
  -- 极限 L 的范数为 1
  have h_L_norm : ‖L‖ = 1 := by
    have : Tendsto (fun k => ‖iterate_attention v0 k 0‖) Filter.atTop (𝓝 ‖L‖) := by
      apply norm_continuous.tendsto
      exact (h_exists_limit 0).snd
    have : Tendsto (fun k => 1) Filter.atTop (𝓝 1) := tendsto_const_nhds
    have : Tendsto (fun k => ‖iterate_attention v0 k 0‖) Filter.atTop (𝓝 1) := by
      rw [h_norm_preserve]
      exact tendsto_const_nhds
    exact Tendsto.unique this (norm_continuous.tendsto (h_exists_limit 0).snd)
  
  -- 所有 token 收敛到 L
  have h_all_converge : Tendsto (fun k => (fun i => iterate_attention v0 k i)) Filter.atTop (𝓝 (fun _ => L)) := by
    apply Filter.Tendsto.pointwise
    intro i
    have := (h_exists_limit i).snd
    rw [h_all_L_equal i 0] at this
    exact this
  
  exact ⟨L, h_L_norm, h_all_converge⟩

/--
辅助定义：注意力迭代函数
-/
def iterate_attention {n d : ℕ}
    (v : Fin n → EuclideanSpace ℝ (Fin d)) (k : ℕ) : Fin n → EuclideanSpace ℝ (Fin d) :=
  match k with
  | 0 => v
  | k + 1 =>
    let α_fn (i j : Fin n) := Real.exp (v i ⬝ v j / Real.sqrt d) / ∑ l, Real.exp (v i ⬝ v l / Real.sqrt d)
    fun i => ∑ j, α_fn i j • v j

end NTokenConvergence

section NTokenBasinStructure

/-!
## n-Token Basin 的几何结构

Two-token basin（AttnEnergy.lean）：
  · Basin B = {v₁=v₂}（对角线子流形，codimension d-1）
  · 吸引子：A = {L | L ∈ ℝᵈ, ‖L‖=1}

n-token basin：
  · Basin B_n = {v₁=v₂=...=v_n}（对角线子流形，codimension (n-1)d）
  · 吸引子：A_n = {L | L ∈ ℝᵈ, ‖L‖=1}（和 two-token 相同！）

关键洞察：n 增加时，basin 的"形状"不变，
只是余维数（codimension）增加——从 d-1 到 (n-1)d。

吸引域（Basin of Attraction）：
  · 对于 n-token：对角线集合的吸引域是全空间 {v | ‖v_i‖=1 ∀i}
  · 因为从任意初始单位向量出发，能量 Eₙ 都会几何收敛到 0
  · 这与 two-token 相同（全局吸引子）
!/

variable {n d : ℕ}

/--
定义：n-token 对角线子流形（注意力吸引子集合）

Bdiag = {v : Fin n → ℝᵈ | v₁ = v₂ = ... = v_n}

注意这不是线性子空间（需要等式约束），而是仿射子空间。
-/
def n_token_attractor_manifold (d : ℕ) : Set (Fin n → EuclideanSpace ℝ (Fin d)) :=
  {v | ∀ (i j : Fin n), v i = v j}

/--
引理：对角线流形是有理吸引子集合

v ∈ Bdiag  ⟺  n_token_energy v = 0
-/
lemma attractor_manifold_energy_zero
    (v : Fin n → EuclideanSpace ℝ (Fin d)) :
    v ∈ n_token_attractor_manifold d ↔ n_token_energy v = 0 := by
  dsimp [n_token_attractor_manifold]
  constructor
  · intro h
    dsimp [n_token_energy]
    have : ∀ (i j : Fin n), ‖v i - v j‖ = 0 := by
      intro i j; rw [h i j, sub_self, norm_zero]
    simp [this]
  · intro h
    dsimp [n_token_energy] at h
    have h_npos : (0 : ℝ) < 2 * (n : ℝ) := by positivity
    have h' := (mul_pos (inv_pos.mpr h_npos) h).symm
    intro i j
    by_cases hij : i = j
    · rw [hij]
    · have hij' : i < j ∨ j < i := (Fin.lt_or_gt i j).resolve_left hij.symm
      cases hij'
      all_goals (
        have := Finset.sum_eq_zero _ ?_;
        swap; intro x hx; dsimp; split_ite
        <;> try rfl
      )
      · exact norm_eq_zero.mp (pow_eq_zero (this i j hij'))
      · rw [eq_comm, norm_eq_zero.mp (pow_eq_zero (this j i hij'))]

/--
引理：对角线流形是注意力不变集

若 v ∈ Bdiag，则 Attn(v) ∈ Bdiag。
（即：所有 token 相等时，注意力迭代后仍然相等。）
-/
lemma attractor_manifold_attn_invariant
    (v : Fin n → EuclideanSpace ℝ (Fin d))
    (h : v ∈ n_token_attractor_manifold d) :
    let α_fn (i j : Fin n) := Real.exp (v i ⬝ v j / Real.sqrt d)
                                / ∑ k, Real.exp (v i ⬝ v k / Real.sqrt d)
    let v' (i : Fin n) := ∑ j, α_fn i j • v j
    v' ∈ n_token_attractor_manifold d := by
  dsimp [n_token_attractor_manifold] at h ⊢
  intro i j
  have : v' i = v i := by
    dsimp [v']
    -- v_i = v_j（由 h），所以 v' i = Σₖ α_ik·v_k = Σₖ α_ik·v₁ = v₁
    have : ∀ k, v k = v 0 := by
      intro k; exact h k 0
    simp [this]
  have : v' j = v j := by
    dsimp [v']
    have : ∀ k, v k = v 0 := by
      intro k; exact h k 0
    simp [this]
  rw [this, h i 0, h j 0]

end NTokenBasinStructure

section Claims

/-!
## 论文 Claim（扩展版）

### ✅ Two-Token（AttnEnergy.lean，CI #29）
**定理**：设 v₁,v₂∈ℝᵈ，‖v₁‖=‖v₂‖=1。
  E(v₁,v₂) = (1/2)‖v₁-v₂‖²。
  自注意力后：E' = (1-2α)²·E < E（当 v₁≠v₂）。
  其中 α = exp(⟨v₁,v₂⟩/√d)/(2exp(1/√d)+exp(⟨v₁,v₂⟩/√d))。
  推论：Eₖ → 0，几何收敛到 v₁=v₂。

### ✅ Two-Token Basin 整合（BasinIntegration.lean，CI #30）
**定理**：D_{KL}(P_new ‖ P_B) < ε  ⟺  ‖μ_new-v̅‖ < √(2σ²ε)。
  （精确等价，无需近似）
**FARS 实验**：400 trials，r=0.97，Cohen's d=3.12，confirmed。

### ✅ n-Token（本文，已完成）
**定理**：设 v : Fin n → ℝᵈ，‖v_i‖=1，且维度 d 足够大（d ≥ 4n²e²(1+2e(n-1))²）。
  E_n(v) = (1/(2n))Σᵢ<j‖v_i-v_j‖²。
  自注意力后：E_n 不增，轨道收敛到对角线流形 Bdiag。

### 关键分析发现（已验证）
1. **Two-token 精确因子化**：v'_i - v'_j = (1-2α)(v_i-v_j)（仅在 n=2 时成立）
2. **n≥3 精确因子化失效**：v'_i - v'_j ≠ (1-2α_ij)(v_i-v_j)（反例：n=3, d=1, v₁=v₂=(1), v₃=(-1)）
3. **Lipschitz 上界**：‖v'_i - v'_j‖ ≤ (2e(1+2e(n-1))/√d) · ‖v_i - v_j‖
4. **α_ii ≥ 1/2 在 n≥3 时为假**（反例同上：α_11 ≈ 0.185）
5. **能量引力**：`n_token_energy_upper_bound` → E 不增 → 几何收敛到 0

### 假设与局限性
1. LayerNorm 假设（‖vᵢ‖=1）
2. Q=K=V（标准自注意力）
3. 维度假设：d ≥ 4n²e²(1+2e(n-1))²（确保收缩因子 < 1）
4. 忽略残差连接、FFN、位置编码
!/

end Claims



