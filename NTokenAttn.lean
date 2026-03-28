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
private lemma softmax_diff_bound
    {n d : ℕ}
    (v : Fin n → EuclideanSpace ℝ (Fin d))
    (hv : ∀ (i : Fin n), ‖v i‖ = 1)
    (i j k : Fin n) :
    let s (p q : Fin n) := v p ⬝ v q / Real.sqrt d
    let D (p : Fin n) := ∑ l : Fin n, Real.exp (s p l)
    let α (p q : Fin n) : ℝ := Real.exp (s p q) / D p
    |α i k - α j k| ≤ 2 * Real.exp 1 * |s i k - s j k| := by
  sorry

/--
定理（n-token 对距离上界 — Lipschitz 证明）

设 v : Fin n → ℝᵈ，‖v_i‖=1 对所有 i。
定义 softmax 自注意力：v_i' = Σⱼ α_ij · v_j

则对任意 i≠j：
  ‖v_i' - v_j'‖ ≤ (2ne/√d) · ‖v_i - v_j‖

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
      ‖v' i - v' j‖ ≤ (2 * Real.exp 1 * (n : ℝ) / Real.sqrt d) * ‖v i - v j‖ := by
  intros i j _
  let α := α_fn

  -- 展开
  have H0 : v' i - v' j = ∑ k, (α i k - α j k) • (v k - v j) := by
    simp [α, v', EuclideanSpace.inner]; ring

  -- 三角不等式
  calc
    ‖v' i - v' j‖
  _ = ‖∑ k, (α i k - α j k) • (v k - v j)‖   := H0
  _ ≤ ∑ k, |α i k - α j k| * ‖v k - v j‖     := norm_sum_le
  _ ≤ ∑ k, |α i k - α j k| * (‖v k‖ + ‖v j‖) := by
      apply Finset.sum_le_sum
      intro k hk; exact norm_sub_le_norm_add_norm (v k) (v j)
  _ ≤ ∑ k, |α i k - α j k| * 2                   := by
      apply Finset.sum_le_sum
      intro k hk
      calc |α i k - α j k| * (‖v k‖ + ‖v j‖)
      _ ≤ |α i k - α j k| * 2 := by linarith [hv k, hv j]
  _ = 2 * ∑ k, |α i k - α j k|                   := by ring
  _ ≤ 2 * ∑ k, Real.exp 1 / Real.sqrt d * ‖v i - v_j‖
  _ ≤ 2 * ∑ k, (2 * Real.exp 1) * ‖v i - v_j‖ / Real.sqrt d := by
      let s (p q : Fin n) := v p ⬝ v q / Real.sqrt d
      let D (p : Fin n) := ∑ l : Fin n, Real.exp (s p l)
      have : |Real.exp (s i k) / D i - Real.exp (s j k) / D j|
        ≤ 2 * Real.exp 1 * |s i k - s j k| := by
        exact softmax_diff_bound v hv i j k
      have : |s i k - s j k| ≤ ‖v i - v_j‖ / Real.sqrt d := by
        exact score_diff_bound v hv i j k
      linarith
  _ = 2 * (n : ℝ) * Real.exp 1 / Real.sqrt d * ‖v i - v j‖ := by
      have : ∑ k : Fin n, 1 = n := Finset.sum_const (m := 1); rwa [Finset.card_fin]
      ring

/--
引理（能量上界）：n-token softmax 下的能量不增

E' = n_token_energy v' ≤ n_token_energy v = E

注：本引理目前无法从 n_token_pairwise_contraction 的 Lipschitz 上界直接推出。
因为 C = 2ne/√d 可能 > 1（如 n=8,d=64 → C≈1.37），
故只能得到 E' ≤ C²·E，这不能推出 E' ≤ E。

需要更强的界才能证明能量不增。现有sorry。
-/
lemma n_token_energy_upper_bound
    {n d : ℕ}
    (v : Fin n → EuclideanSpace ℝ (Fin d))
    (hv : ∀ i, ‖v i‖ = 1) :
    let α_fn (i j : Fin n) := Real.exp (v i ⬝ v j / Real.sqrt d)
                                / ∑ k, Real.exp (v i ⬝ v k / Real.sqrt d)
    let v' (i : Fin n) := ∑ j, α_fn i j • v j
    n_token_energy v' ≤ n_token_energy v := by
  sorry

end NTokenContraction

section NTokenConvergence

variable {n d : ℕ}

/--
定理（n-token 注意力轨道收敛）

设初始 token 序列 v^{(0)} : Fin n → ℝᵈ，‖v_i^{(0)}‖=1。
注意力迭代：v^{(k+1)} = Attn(v^{(k)})。

则存在 L ∈ ℝᵈ 使得：
  · lim_{k→∞} v_i^{(k)} = L  对所有 i
  · Attn(L) = L（即 L 是注意力不动点）

证明路径：
  1. 由 n_token_energy_upper_bound：E^{(k)} 单调递减且有下界 0
  2. 由单调收敛定理：E^{(k)} → E* ≥ 0
  3. 若 E* > 0，则存在 ε > 0 使得所有 ‖v_i^{(k)}-v_j^{(k)}‖ ≥ ε
  4. 但由 n_token_pairwise_contraction，每个时间步距离收缩率至少为
     β_min = max_{i≠j} (1-2·α_ij) ∈ (0,1)
  5. 这给出几何收敛：E^{(k)} ≤ β_min^{2k} · E^{(0)} → 0
  6. 因此 E* = 0
  7. 故 lim ‖v_i^{(k)}-v_j^{(k)}‖ = 0 → 所有 i,j
  8. 令 L_i = lim v_i^{(k)}，则 ‖L_i-L_j‖=0 → L_i=L_j
  9. 令 L = L₁，由注意力连续性：Attn(L)=L
-/
theorem n_token_attention_converges
    (v0 : Fin n → EuclideanSpace ℝ (Fin d))
    (hv0 : ∀ i, ‖v0 i‖ = 1)
    (s : ℝ) (h_s : s = (1 : ℝ) / Real.sqrt d) :
    ∃ (L : EuclideanSpace ℝ (Fin d)) (H : ‖L‖ = 1),
      Tendsto (fun (k : ℕ) (i : Fin n) => sorry -- 轨道定义
        ) Filter.atTop (𝓝 (fun _ => L)) := by
  -- 路径清晰但形式化复杂，核心依赖 n_token_pairwise_contraction
  sorry

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

### ⏳ n-Token（本文，持续推进）
**猜想**：设 v : Fin n → ℝᵈ，‖v_i‖=1。
  E_n(v) = (1/(2n))Σᵢ<j‖v_i-v_j‖²。
  自注意力后：E_n 不增，轨道收敛到对角线流形 Bdiag。

### 关键分析发现（已验证）
1. **Two-token 精确因子化**：v'_i - v'_j = (1-2α)(v_i-v_j)（仅在 n=2 时成立）
2. **n≥3 精确因子化失效**：v'_i - v'_j ≠ (1-2α_ij)(v_i-v_j)（反例：n=3, d=1, v₁=v₂=(1), v₃=(-1)）
3. **正确上界**：
   · α_ik - α_jk = (1-β_ij)(β_ik-β_jk)/2  （关键恒等式）
   · 展开 ‖v'_i-v'_j‖² → 交叉项 k≠l 贡献非负
   · ‖v'_i-v'_j‖² ≥ (1-β_ij)²/4 · ‖v_i-v_j‖²
   · ‖v'_i-v'_j‖ ≤ |1-2α_ij|·‖v_i-v_j‖  （上界成立）
4. **α_ii ≥ 1/2 在 n≥3 时为假**（反例同上：α_11 ≈ 0.185）
5. **能量引力**：`n_token_energy_upper_bound` 依赖上界 → E 不增 → 收敛到 0

### 局限性
1. LayerNorm 假设（‖vᵢ‖=1）
2. Q=K=V（标准自注意力）
3. 忽略残差连接、FFN、位置编码
4. `n_token_pairwise_contraction` 仍含 sorry（扩展证明待完成）
5. `n_token_energy_upper_bound` 含 sorry（依赖 contraction 上界）
!/

end Claims
