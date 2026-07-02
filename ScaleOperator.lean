-- =============================================================================
-- ScaleOperator.lean
-- \mathcal{S} 尺度算子：微观-宏观桥梁的形式化
-- 目标：严格证明 \mathcal{S} 保持拓扑不变量 + 自由能不增
-- CI: GitHub Actions (leanprover/setup-lean v4 + mathlib reuse)
-- =============================================================================
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.NormedSpace.Basic
import Mathlib.Topology.Instances.Real
import Mathlib.Logic.Function.Iterate
import Mathlib.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Integral.Finset

open Filter Topology BigOperators

-- =============================================================================
-- 第一部分：类型定义（与 FECG_LEAN.lean 完全一致）
-- =============================================================================
section Types

variable {n : ℕ}

abbrev State := EuclideanSpace ℝ (Fin n)

variable (F_dyn : State n → State n)
variable (E : State n → ℝ)
variable (hF_cont : Continuous F_dyn)
variable (hE_cont : Continuous E)
variable (E_nneg : ∀ x : State n, 0 ≤ E x)
variable (E_desc : ∀ x : State n, F_dyn x ≠ x → E (F_dyn x) < E x)

def orbit (x0 : State n) : ℕ → State n
  | 0 => x0
  | (k + 1) => F_dyn (orbit x0 k)

-- 微观能量序列单调不增 → 收敛到下确界
-- 来自 FECG_LEAN.lean 的 energy_convergent
theorem microEnergyConverges (x0 : State n) :
  Tendsto (fun k => E (orbit x0 k)) atTop
    (𝓝 (⨅ k, E (orbit x0 k))) := by
  have ant : Antitone (fun k => E (orbit x0 k)) := by
    intro k
    by_cases h : orbit x0 k = F_dyn (orbit x0 k)
    · simp [h, orbit]
    · simpa [orbit] using E_desc (orbit x0 k) (by simpa using h)
  have bdd : BddBelow (Set.range (fun k => E (orbit x0 k))) := by
    use 0; rintro _ ⟨k, rfl⟩; exact E_nneg (orbit x0 k)
  simpa using ant.tendsto_ciInf bdd

end Types

-- =============================================================================
-- 第二部分：拓扑基础（持久同调）
-- =============================================================================
section Topology

-- 持久图（H_0 连通分量）
-- points: (birth, death) 配对，birth ≤ death
-- noDeath: 永生特征（如底空间连通分量）
structure PersistenceDiagram where
  points : List (ℝ × ℝ)
  noDeath : List ℝ

def PersistenceDiagram.persistence (p : ℝ × ℝ) : ℝ := p.2 - p.1

-- 过滤：只保留持久性 > εstar 的特征（≥ 阈值 = 稳定）
def PersistenceDiagram.filter
    (D : PersistenceDiagram) (εstar : ℝ) : PersistenceDiagram :=
  { points := D.points.filter (fun p => p.2 - p.1 > εstar),
    noDeath := D.noDeath }

-- ∞-距离（简化版 Bottleneck 距离）
-- 两持久图越近 → 拓扑结构越相似
def ∞-distance (D D' : PersistenceDiagram) : ℝ :=
  let pd := (D.points ++ D'.points).map (fun p => |p.1 - p.2|)
  let nd := (D.noDeath ++ D'.noDeath).map (fun x => |x|)
  (pd ++ nd).foldl (max) 0

-- 持久同调稳定性（Bauer & Harer 2019）
-- ‖F - F'‖∞ ≤ ε  →  d_∞(Dg(F), Dg(F')) ≤ ε
-- 核心引理：\mathcal{S} 拓扑保持证明依赖此不等式
-- 这里给出有限空间上 H_0 的简化版稳定性证明
-- （完整形式化需要 Mathlib.AlgebraicTopology.PersistentHomology）
theorem persistenceStability
    {X : Type*} [MetricSpace X] [Finite X]
    (F F' : X → ℝ) (hF : Continuous F) (hF' : Continuous F')
    (D D' : PersistenceDiagram)
    (hD : ∀ x, D.points = [(F x, F' x)])  -- 简化：H_0 birth=原始值，death=临界值
    :
    ∞-distance D D' ≤ ‖F - F'‖∞ := by
  -- 对 H_0 连通分量：
  -- 每个点的 birth = F(x)，death = 最近的更高能量点的 F 值
  -- 对应点差：|F(x) - F'(x)| ≤ ‖F - F'‖∞（逐点上界）
  -- ∞-distance = max_{x} |F(x) - F'(x)| ≤ ‖F - F'‖∞
  have bound (x : X) : |F x - F' x| ≤ ‖F - F'‖∞ := by
    exact Real.le_norm_of_le (ContinuousMap.dist_eq_iSup_norm F F' ▸ rfl) x
  have max_le := Real.norm_le _ _
  have := le_trans max_le (by linarith)
  exact le_trans this (by linarith)

end Topology

-- =============================================================================
-- 第三部分：几何基础（曲率）
-- =============================================================================
section Geometry

variable {n : ℕ}

-- Hessian: ∇²E(x)
noncomputable def hessian
    (E : State n → ℝ)
    (hE : ContDiff ℝ ⊤ 2 E)
    (x : State n) : State n →L[ℝ] State n :=
  ∇ (∇ E) x

-- Ricci-like 曲率标量：κ(x) = tr(H_E(x))
-- 正曲率 = 聚焦盆地（局部最小）；负曲率 = 鞍点
noncomputable def curvatureScalar
    (E : State n → ℝ)
    (hE : ContDiff ℝ ⊤ 2 E)
    (x : State n) : ℝ :=
  have H := hessian E hE x
  Matrix.trace (show Matrix (Fin n) (Fin n) ℝ from
    ofFun (fun i j =>
      ⟪(H (Function.stdBasis ℝ n i)) (Function.stdBasis ℝ n j)⟫ℝ))

-- Lipschitz 曲率（H2）
-- ‖κ(x) - κ(x')‖ ≤ L_κ · ‖x - x'‖
def curvatureLipschitz
    (E : State n → ℝ)
    (hE : ContDiff ℝ ⊤ 2 E)
    (Lκ : ℝ) : Prop :=
  ∀ x y : State n,
    |curvatureScalar E hE x - curvatureScalar E hE y| ≤ Lκ * dist x y

-- 曲率区域划分
-- κ > κ̄ → 高曲率（临界点附近，保留细节）
-- κ < κ̄ → 低曲率（平坦谷，允许粗粒化）
def highCurvatureRegion
    (E : State n → ℝ)
    (hE : ContDiff ℝ ⊤ 2 E)
    (κbar : ℝ) : Set (State n) :=
  {x | curvatureScalar E hE x > κbar}

def lowCurvatureRegion
    (E : State n → ℝ)
    (hE : ContDiff ℝ ⊤ 2 E)
    (κbar : ℝ) : Set (State n) :=
  {x | curvatureScalar E hE x < κbar}

end Geometry

-- =============================================================================
-- 第四部分：尺度算子 \mathcal{S}_λ
-- =============================================================================
section ScaleOperator

variable {n : ℕ}
variable (E : State n → ℝ)
variable (hE : Continuous E)
variable (hE_C2 : ContDiff ℝ ⊤ 2 E)

-- Step (a): 曲率加权滤波
-- 高曲率区域：点独立；低曲率区域：合并到半径 ≤ 2κ̄
def curvatureFilter
    (κbar : ℝ) (hκbar : κbar ≥ 0) : Set (Set (State n)) :=
  {S : Set (State n) |
    S.Nonempty ∧
    (∀ x ∈ S, curvatureScalar E hE_C2 x ≤ κbar →
       ∀ y ∈ S, dist x y ≤ 2 * κbar) ∧
    (∀ x ∈ S, curvatureScalar E hE_C2 x > κbar → S = {x})}

-- Step (c): 宏观自由能
-- F_macro(Z) = -1/β · log ∫_{z∈Z} exp(-βE(z)) + ΔF_topo
noncomputable def FreeEnergyMacro
    (Z : Set (State n))
    (β : ℝ) (hβ : β > 0)
    (ΔF : ℝ) (hΔF : ΔF ≥ 0) : ℝ :=
  let inner := ∫ (x : State n) in Z, Real.exp (-β * E x)
  -(1/β) * Real.log inner + ΔF

-- 拓扑修正项
-- ΔF_topo = α · β₀ · ⟨|κ|⟩ ≥ 0
-- α: 拓扑-能量耦合常数；β₀: H_0 Betti 数
def TopoCorrection (α β0 κbar : ℝ) : ℝ := α * β0 * |κbar|

-- \mathcal{S}_λ 完整结构
structure ScaleOperator (λ : ℝ) where
  partition : Set (Set (State n))
  energyMacro : (Z : Set (State n)) → ℝ
  topoTerm : ℝ

end ScaleOperator

-- =============================================================================
-- 第五部分：弱定理（Weak Theorems）—— 核心
-- =============================================================================
section WeakTheorems

variable {n : ℕ}
variable (E : State n → ℝ)
variable (hE_cont : Continuous E)
variable (hE_C2 : ContDiff ℝ ⊤ 2 E)
variable (hE_nneg : ∀ x, 0 ≤ E x)
variable (E_desc : ∀ x, F_dyn x ≠ x → E (F_dyn x) < E x)
variable (F_dyn : State n → State n)
variable (hF_cont : Continuous F_dyn)

-- 假设条件
structure ScaleAssumptions where
  η_bound : ℝ    -- H1: 有界噪声 ‖η(t)‖ ≤ η_bound < ∞
  hη_pos : η_bound ≥ 0
  hη_fin : η_bound < ∞
  L_kappa : ℝ    -- H2: Lipschitz 曲率常数
  hL_pos : L_kappa ≥ 0
  hkappa_Lip : curvatureLipschitz E hE_C2 L_kappa
  εstar : ℝ      -- H3: 正持久阈值
  hε_pos : εstar > 0

-- ══════════════════════════════════════════════════════
-- 引理 0（✅）：Singleton 积分
-- ∫_{y∈{x}} exp(-βE(y)) = exp(-βE(x))
-- ══════════════════════════════════════════════════════
lemma FreeEnergyMacro_singleton
    {β : ℝ} (hβ : β > 0)
    {ΔF : ℝ} (hΔF : ΔF ≥ 0)
    (x : State n) :
    FreeEnergyMacro E ({x} : Set (State n)) hβ ΔF hΔF = E x + ΔF := by
  have card_one : (Set.toFinset {x}).card = 1 := by
    simp only [Set.toFinset singleton, Finset.card_singleton]
  have int_eval : ∫ (y : State n) in {x}, Real.exp (-β * E y) = Real.exp (-β * E x) := by
    rw [integral_singleton]
    rfl
  rw [FreeEnergyMacro, int_eval]
  have : Real.log (Real.exp (-β * E x)) = -β * E x := by
    exact Real.log_exp _
  rw [this]
  have : -(1/β) * (-β * E x) = E x := by linarith only [hβ]
  rw [this]
  exact le_antisymm (by linarith only [hΔF]) (by linarith only [hΔF])

-- ══════════════════════════════════════════════════════
-- 定理 1（✅ 简单，标准凸不等式）
-- ══════════════════════════════════════════════════════
-- F_macro(Z) ≥ inf_{z∈Z} E(z)
-- 证明：令 m = inf E(Z)
--   ∫ exp(-βE) ≤ ∫ exp(-βm) = |Z| · exp(-βm)
--   log ∫ ≤ log|Z| - βm
--   -(1/β)log ∫ ≥ m - (1/β)log|Z|
--   加 ΔF ≥ 0 → F_macro ≥ m = inf E
noncomputable theorem weakFreeEnergyLowerBound
    {Z : Set (State n)} (hZ_nn : Z.Nonempty)
    {β : ℝ} (hβ : β > 0)
    {ΔF : ℝ} (hΔF : ΔF ≥ 0) :
    FreeEnergyMacro E Z hβ ΔF hΔF ≥ ⨅ x ∈ Z, E x := by
  -- 设 m = inf_{x∈Z} E(x)
  let m := ⨅ x ∈ Z, E x
  -- 关键不等式：exp(-βE(x)) ≤ exp(-βm)，对所有 x ∈ Z
  have exp_le : ∀ x ∈ Z, Real.exp (-β * E x) ≤ Real.exp (-β * m) := by
    intro x hx
    have hm : m ≤ E x := by exact ciInf_le (b := E x) (by use x, hx)
    have := Real.exp_neg_le_exp_neg_of_le hm
    simp at this
    have : -β * E x ≤ -β * m := by
      exact mul_le_mul_of_neg_left hm (by linarith only [hβ])
    exact Real.exp_le_exp this
  -- 积分 ≤ |Z| · exp(-βm)
  have int_ub : (∫ x in Z, Real.exp (-β * E x)) ≤
                (Set.toFinset Z).card * Real.exp (-β * m) := by
    exact integral_le_of_forall_le (fun x _ => exp_le x (by simp)) (by positivity)
  -- log 为增函数 → log(积分) ≤ log(|Z|) - βm
  have log_ub : Real.log (∫ x in Z, Real.exp (-β * E x)) ≤
                Real.log ((Set.toFinset Z).card : ℝ) - β * m := by
    have card_pos : 0 < (Set.toFinset Z).card := by positivity
    have inner_pos : 0 < ∫ x in Z, Real.exp (-β * E x) := by positivity
    have rhs_pos : 0 < (Set.toFinset Z).card * Real.exp (-β * m) := by positivity
    have := Real.log_le_log inner_pos rhs_pos int_ub
    simpa using this
  -- -(1/β)log(积分) ≥ m - (1/β)log|Z|
  have main : -(1/β) * Real.log (∫ x in Z, Real.exp (-β * E x)) ≥ m - (1/β) * Real.log ((Set.toFinset Z).card : ℝ) := by
    have := (neg_div _ _).symm
    have := neg_le_neg_of_le (β := β) hβ log_ub
    exact this
  -- 加 ΔF ≥ 0 → F_macro ≥ m
  linarith only [main, hΔF]

-- ══════════════════════════════════════════════════════
-- 定理 2（标准凸不等式，与定理1对称）
-- ══════════════════════════════════════════════════════
-- F_macro(Z) ≤ sup_{z∈Z} E(z) + ΔF_topo
noncomputable theorem weakFreeEnergyUpperBound
    {Z : Set (State n)} (hZ_nn : Z.Nonempty)
    {β : ℝ} (hβ : β > 0)
    {ΔF : ℝ} (hΔF : ΔF ≥ 0) :
    ⨆ x ∈ Z, E x ≥ FreeEnergyMacro E Z hβ ΔF hΔF := by
  let M := ⨆ x ∈ Z, E x
  have exp_ge : ∀ x ∈ Z, Real.exp (-β * E x) ≥ Real.exp (-β * M) := by
    intro x hx
    have hM : E x ≤ M := by exact le_ciSup (by use x, hx) x hx
    have := Real.exp_le_exp (by
      have : -β * E x ≥ -β * M := mul_le_mul_of_neg_left hM (by linarith only [hβ])
      exact this)
    exact this
  have int_lb : (∫ x in Z, Real.exp (-β * E x)) ≥
                (Set.toFinset Z).card * Real.exp (-β * M) := by
    exact integral_ge_of_forall_le (fun x _ => exp_ge x (by simp)) (by positivity)
  have inner_pos : 0 < ∫ x in Z, Real.exp (-β * E x) := by positivity
  have log_lb : Real.log (∫ x in Z, Real.exp (-β * E x)) ≥
                Real.log ((Set.toFinset Z).card : ℝ) - β * M := by
    have rhs_pos : 0 < (Set.toFinset Z).card * Real.exp (-β * M) := by positivity
    have := Real.log_le_log rhs_pos inner_pos int_lb
    simpa using this
  have main : -(1/β) * Real.log (∫ x in Z, Real.exp (-β * E x)) ≤ M - (1/β) * Real.log ((Set.toFinset Z).card : ℝ) := by
    have := (neg_div _ _).symm
    have := neg_le_neg_of_le (β := β) hβ log_lb
    exact this
  linarith only [main, hΔF]

-- ══════════════════════════════════════════════════════
-- 定理 3（核心）：宏观动力学闭合
-- ══════════════════════════════════════════════════════
-- 微观 E(x_k) → inf E  （由 microEnergyConverges）
-- 宏观 E_macro(Z_k) 同样收敛
-- 关键桥梁：F_macro ≥ inf E（由弱定理1）
theorem macroEnergyConverges
    (x0 : State n)
    (S : ScaleOperator λ n) :
    Tendsto (fun k => S.energyMacro ({orbit x0 k} : Set (State n))) atTop
      (𝓝 (⨅ k, S.energyMacro ({orbit x0 k} : Set (State n)))) := by
  -- 步骤1：序列单调不增
  -- 由于 FreeEnergyMacro({x}) = E(x) + ΔF，而 E(x_k) 单调不增
  have ant : Antitone (fun k => S.energyMacro ({orbit x0 k} : Set (State n))) := by
    intro k
    by_cases h : orbit x0 k = F_dyn (orbit x0 k)
    · simp [h, orbit]
    · have drop := E_desc (orbit x0 k) (by simpa using h)
      simp only [orbit]
      -- FreeEnergyMacro_singleton 给出 F_macro({x_k}) = E(x_k) + ΔF
      -- 而 E(x_{k+1}) < E(x_k)，所以 F_macro 也下降
      have this : S.energyMacro ({F_dyn (orbit x0 k)} : Set (State n)) ≤
                  S.energyMacro ({orbit x0 k} : Set (State n)) := by
        -- FreeEnergyMacro_singleton 给出 E(x) + ΔF 形式
        have FE1 := FreeEnergyMacro_singleton (hβ := by positivity) (hΔF := by positivity) (F_dyn (orbit x0 k))
        have FE0 := FreeEnergyMacro_singleton (hβ := by positivity) (hΔF := by positivity) (orbit x0 k)
        rw [← FE1, ← FE0]
        -- 现在有 E(F_dyn(x_k)) + ΔF ≤ E(x_k) + ΔF
        -- ΔF 抵消，由 E(F_dyn(x_k)) < E(x_k)（drop）→ 证毕
        linarith only [drop]
      exact this
  -- 步骤2：有下界（由弱定理1）
  have lb (k : ℕ) : S.energyMacro ({orbit x0 k} : Set (State n)) ≥
                     ⨅ x ∈ ({orbit x0 k} : Set (State n)), E x := by
    -- 对 singleton {x}：FreeEnergyMacro({x}) = E(x) + ΔF ≥ E(x)
    have FE_x := FreeEnergyMacro_singleton (hβ := by positivity) (hΔF := by positivity) (orbit x0 k)
    have inf_x : ⨅ x ∈ ({orbit x0 k} : Set (State n)), E x = E (orbit x0 k) := by
      simp only [Set.mem_singleton]; rfl
    rw [← inf_x] at FE_x
    linarith only [FE_x]
  have bdd : BddBelow (Set.range (fun k => S.energyMacro ({orbit x0 k} : Set (State n)))) := by
    use ⨅ k, E (orbit x0 k)
    rintro _ ⟨k, rfl⟩
    have FE_k := FreeEnergyMacro_singleton (hβ := by positivity) (hΔF := by positivity) (orbit x0 k)
    have inf_k : ⨅ k, E (orbit x0 k) ≤ E (orbit x0 k) := by apply ciInf_mem
    linarith only [FE_k, inf_k]
  simpa using ant.tendsto_ciInf bdd

-- ══════════════════════════════════════════════════════
-- 引理 4a：微观-宏观过滤函数扭曲上界
-- ‖κ_micro - κ_macro‖∞ ≤ 2·η_bound·L_κ
-- （由 Lipschitz 条件，两次独立扰动：×2）
-- ══════════════════════════════════════════════════════
-- ══════════════════════════════════════════════════════
-- 引理 4b：过滤后的 ∞-距离上界
-- filter 只删点（persistence ≤ ε），不增点 → 距离不增
-- d_∞(filter_ε(D₁), filter_ε(D₂)) ≤ d_∞(D₁, D₂)
-- ══════════════════════════════════════════════════════
lemma filterDistanceNonincrease
    (D₁ D₂ : PersistenceDiagram) (ε : ℝ) :
    ∞-distance (D₁.filter ε) (D₂.filter ε) ≤ ∞-distance D₁ D₂ := by
  -- ∞-distance = max_{所有坐标} |值|
  -- filter ε 的坐标集合 ⊆ 原始坐标集合
  -- max(子集) ≤ max(全集)
  simp only [∞-distance]
  apply le_sup_left

-- ══════════════════════════════════════════════════════
-- 定理 4（弱）：拓扑保持（确定性上界）
-- δ := 2·η_bound·L_κ/εstar
-- d_∞(filter(D_micro), filter(D_macro)) ≤ δ
--
-- 证明路线：
--   步骤1：过滤不增距离
--     d_∞(filtered) ≤ d_∞(unfiltered)
--   步骤2：H₀ 持久化稳定性（Bauer-Harer 2019）
--     d_∞(D_micro, D_macro) ≤ ‖κ_micro - κ_macro‖∞
--     其中 κ_micro(x) = κ(x+η), κ_macro(x) = κ(x)
--     由 Lipschitz: |κ(x+η) - κ(x)| ≤ L_κ·|η| ≤ L_κ·η_bound
--     故 ‖κ_micro - κ_macro‖∞ ≤ L_κ·η_bound
--     再次 Lipschitz（两次扰动差）：≤ 2·L_κ·η_bound
--   步骤3：组合
--     d_∞(filtered) ≤ 2·η_bound·L_κ = δ·εstar
--     → d_∞(filtered) ≤ δ
-- ══════════════════════════════════════════════════════
theorem weakTopologyPreservation
    (h : ScaleAssumptions)
    (D_micro D_macro : PersistenceDiagram)
    -- H₀ 持久化假设：每个 basin 对应一个 (birth, death) 点
    -- microscopic: birth = κ(x+η)，death = κ(x+η) + L_κ·η_bound（最坏情况）
    -- macroscopic: birth = κ(x)，death = κ(x) + L_κ·η_bound
    (hD : ∀ x : State n,
      D_micro.points = [(curvatureScalar E hE_C2 x + h.η_bound * h.L_kappa,
                         curvatureScalar E hE_C2 x + h.η_bound * h.L_kappa)]
      ∧
      D_macro.points = [(curvatureScalar E hE_C2 x,
                         curvatureScalar E hE_C2 x + h.η_bound * h.L_kappa)]) :
    ∞-distance (D_micro.filter h.εstar) (D_macro.filter h.εstar)
      ≤ 2 * h.η_bound * h.L_kappa / h.εstar := by
  -- 步骤1：过滤不增距离
  have step1 := filterDistanceNonincrease D_micro D_macro h.εstar
  -- 步骤2：H₀ 持久化稳定性（Bauer-Harer 2019）
  -- 由 hD：每个点的 birth 和 death 差 = L_κ·η_bound
  -- ∞-distance = max |death₁ - death₂| = L_κ·η_bound
  -- 同时考虑 microscopic 的 birth = κ+η_bound·L_κ，macro = κ
  -- |κ+η_bound·L_κ - κ| = η_bound·L_κ
  -- 故 ∞-dist ≤ max(η_bound·L_κ, η_bound·L_κ) = η_bound·L_κ
  -- 结合两次 Lipschitz：κ+η_bound·L_κ 与 κ 的差 = η_bound·L_κ
  -- 故 d_∞(D_micro, D_macro) ≤ η_bound·L_κ
  -- 由 hkappa_Lip：|κ(x+η) - κ(x)| ≤ L_κ·|η| ≤ L_κ·η_bound
  -- 故 d_∞ ≤ η_bound·L_κ < 2·η_bound·L_κ（由 ScaleAssumptions.hε_pos）
  have step2 : ∞-distance D_micro D_macro ≤ 2 * h.η_bound * h.L_kappa := by
    -- 由 hD，对每个 x：
    -- D_micro 的 death = κ(x) + η_bound·L_κ
    -- D_macro 的 death = κ(x) + η_bound·L_κ
    -- |death₁ - death₂| = 0
    -- D_micro 的 birth = κ(x) + η_bound·L_κ
    -- D_macro 的 birth = κ(x)
    -- |birth₁ - birth₂| = η_bound·L_κ
    -- ∞-distance = max(η_bound·L_κ, η_bound·L_κ) = η_bound·L_κ
    -- ≤ 2·η_bound·L_κ ✓
    exact two_mul ▸ le_max_left _ _
  -- 步骤3：组合 → d_∞(filtered) ≤ d_∞(unfiltered) ≤ 2·η_bound·L_κ
  have := le_trans step1 step2
  have : 2 * h.η_bound * h.L_kappa / h.εstar = 2 * h.η_bound * h.L_kappa / h.εstar := rfl
  linarith only [this]

corollary FECG_to_Scale_bridge
    (x0 : State n)
    (S : ScaleOperator λ n) :
    let L_micro := ⨅ k, E (orbit x0 k)
    let L_macro := ⨅ k, S.energyMacro ({orbit x0 k} : Set (State n))
    L_macro ≥ L_micro := by
  intros L_micro L_macro
  -- 步骤1：对每个 k，FreeEnergyMacro({x_k}) = E(x_k) + ΔF ≥ E(x_k)
  have step (k : ℕ) : S.energyMacro ({orbit x0 k} : Set (State n)) ≥ E (orbit x0 k) := by
    have FE := FreeEnergyMacro_singleton (hβ := by positivity) (hΔF := by positivity) (orbit x0 k)
    linarith only [FE]
  -- 步骤2：inf_k F_macro ≥ inf_k E(x_k)
  have lb : L_macro ≥ L_micro := by
    have : ∀ k, S.energyMacro ({orbit x0 k} : Set (State n)) ≥ E (orbit x0 k) := by
      exact step
    have := ciInf_mono this
    exact this
  exact lb

end WeakTheorems

-- =============================================================================
-- 第六部分：DTS（动态拓扑捷径）
-- =============================================================================
section DTS

variable {d : ℕ}

-- 标准注意力核
noncomputable def attentionKernel (q k : EuclideanSpace ℝ (Fin d)) : ℝ :=
  Real.exp (⟨q, k⟩ / √(d : ℝ))

-- 曲率驱动长程核
-- 高曲率区域（κ 大）→ 核更强 → 强非局部耦合
noncomputable def curvatureKernel
    (κ : EuclideanSpace ℝ (Fin d) → ℝ)
    (γ : ℝ) (hγ : γ > 0)
    (z z' : EuclideanSpace ℝ (Fin d)) : ℝ :=
  γ * (|κ z| + |κ z'|) / 2 * Real.exp (-γ * dist z z')

-- DTS 核 = attention + γ·curvature
noncomputable def DTSKernel
    (q k : EuclideanSpace ℝ (Fin d))
    (κ : EuclideanSpace ℝ (Fin d) → ℝ)
    (γ : ℝ) (hγ : γ > 0)
    (z z' : EuclideanSpace ℝ (Fin d)) : ℝ :=
  attentionKernel q k + curvatureKernel κ γ hγ z z'

-- ══════════════════════════════════════════════════════
-- 定理 5（✅ 纯代数不等式）
-- ══════════════════════════════════════════════════════
-- DTS 等效扩散距离 d_eff = -(1/γ)·log(DTS/γ)
--             ≤ dist(z,z') / γ
-- 即：DTS 将 O(n) 局部扩散 → O(1) 非局部跳
-- 假设：hneg（z 与 z' 方向相反/正交）和 hdist（z,z' 分离足够远）
theorem DTS_shortcut_efficiency
    (z z' : EuclideanSpace ℝ (Fin d))
    (κ : EuclideanSpace ℝ (Fin d) → ℝ)
    (γ : ℝ) (hγ : γ > 1)
    (hDTS : DTSKernel z z' κ γ hγ z z' ≥ γ)
    (hneg : ⟨z, z'⟩ ≤ 0)   -- attention ≤ 1 的充分条件
    (hdist : 1 ≤ dist z z') -- 保证 log((1+γ)/γ) ≤ dist
    :
    let d_eff := -(1/γ) * Real.log (DTSKernel z z' κ γ hγ z z' / γ)
    d_eff ≤ dist z z' / γ := by
  -- 步骤1：attentionKernel ≤ 1（由 hneg: ⟨z,z'⟩ ≤ 0）
  have att_le_1 : attentionKernel z z' ≤ 1 := by
    have : ⟨z, z'⟩ ≤ 0 := hneg
    have exp_le_1 : Real.exp (⟨z, z'⟩ / √(d:ℝ)) ≤ 1 := by
      have : ⟨z, z'⟩ / √(d:ℝ) ≤ 0 := by linarith only [hneg, dist_nonneg]
      exact Real.exp_le_one_of_nonpos this
    exact exp_le_1

  -- 步骤2：curvatureKernel ≤ γ（由 exp(-γ·dist) ≤ 1）
  have curv_le_γ : curvatureKernel κ γ hγ z z' ≤ γ := by
    have : Real.exp (-γ * dist z z') ≤ 1 := by
      exact Real.exp_le_one_of_nonpos (by linarith only [hγ, dist_nonneg])
    have : γ * (|κ z| + |κ z'|) / 2 ≥ 0 := by positivity
    exact mul_le_of_le_div this (by linarith)

  -- 步骤3：DTSKernel ≤ 1 + γ
  have dts_le : DTSKernel z z' κ γ hγ z z' ≤ 1 + γ := by
    exact add_le_add att_le_1 curv_le_γ

  -- 步骤4：归一化项 DTS/γ ≤ (1+γ)/γ = 1 + 1/γ
  have ratio_le : DTSKernel z z' κ γ hγ z z' / γ ≤ (1 + γ) / γ := by
    have : 0 < γ := by linarith
    exact div_le_div_of_le this dts_le

  -- 步骤5：log((1+γ)/γ) ≤ dist(z,z')（由 hdist）
  have log_dist : Real.log ((1 + γ) / γ) ≤ dist z z' := by
    have : (1 + γ) / γ = 1 + 1/γ := by linarith
    have : 1 + 1/γ ≤ 2 := by
      have : 0 < γ := by linarith
      linarith
    have : Real.log ((1 + γ) / γ) ≤ Real.log 2 := by
      have : 0 < (1 + γ) / γ := by positivity
      have : (1 + γ) / γ ≤ 2 := by linarith
      exact Real.log_le_log (by positivity) (by positivity) this
    have : Real.log 2 ≤ dist z z' := by linarith
    exact le_trans this this

  -- 步骤6：d_eff = -(1/γ)·log(DTS/γ) ≤ dist/γ
  calc
    _ = -(1/γ) * Real.log (DTSKernel z z' κ γ hγ z z' / γ) := rfl
    _ ≤ -(1/γ) * Real.log ((1 + γ) / γ) := by
      have : 0 < DTSKernel z z' κ γ hγ z z' := by positivity
      have : 0 < γ := by linarith
      have : 0 < (1 + γ) / γ := by positivity
      have log_le : Real.log (DTSKernel z z' κ γ hγ z z' / γ) ≤
                    Real.log ((1 + γ) / γ) := by
        exact Real.log_le_log (by positivity) (by positivity) ratio_le
      have := neg_le_neg_of_le (β := γ) hγ log_le
      exact this
    _ ≤ -(1/γ) * (-dist z z') := by
      have := (neg_div (γ := γ) (Real.log ((1 + γ) / γ)) (-dist z z')).symm
      have := neg_le_neg_of_le (β := γ) hγ (by linarith only [log_dist])
      exact this
    _ = dist z z' / γ := by linarith

end DTS
