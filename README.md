# FECG_LEAN: Formalized Energy-Based Concept Generation
# 热力学吸引子动力学的 Lean4 形式化证明

[![License: MIT](https://img.shields.io/badge/License-MIT-blue.svg)](https://opensource.org/licenses/MIT)
[![Lean 4](https://img.shields.io/badge/Lean-4-8957e5?style=flat)](https://leanprover.github.io)
[![Mathlib](https://img.shields.io/badge/Mathlib-latest-ea8805?style=flat)](https://mathlib.harrywu.ml)

**EN**: This repository provides machine-verified (Lean 4 + Mathlib) proofs of attractor dynamics in neural networks — the theoretical foundation of [Thermodynamic AGI (ASI)](https://github.com/simulai/ASI).

**ZH**: 本仓库提供神经网络吸引子动力学的机器验证（Lean 4 + Mathlib）形式化证明——[热力学解析智能 (ASI)](https://github.com/simulai/ASI) 的理论基础。

---

## 📖 Overview / 概述

| EN | ZH |
|----|----|
| Every intelligent system minimizes free energy — this is a **physical law**, not a metaphor. | 任何智能系统都在最小化自由能——这是**物理定律**，不是比喻。 |
| FECG_LEAN proves this mathematically: energy bounded + monotone decreasing → attractor exists. | FECG_LEAN 用数学证明：能量有下界 + 单调不增 → 吸引子存在。 |
| This is the **formal foundation** for Paper 2: Thermodynamic Foundations of Non-QKV Attention. | 这是 **Paper 2（热力学基础）** 的形式化基础。 |

---

## 📁 Lean 4 Source Files

| File | Key Definitions & Theorems |
|------|---------------------------|
| **`FECG_LEAN.lean`** | `energy_antitone`, `energy_convergent`, `fixed_point_of_limit` |
| **`Composite.lean`** | `composite_energy_converges`, `composite_limit_is_fixed_point`, `async_energy_converges`, `robust_async_energy_converges` |
| **`MultiModal.lean`** | `joint_energy_converges`, `attractor_exists_on_compact`, `lasalle_stability` |
| **`lakefile.lean`** | Project configuration + Mathlib dependency |
| **`report.md`** | Full theory documentation (Chinese) |

---

## 🔬 Core Theorems

### FECG_LEAN.lean — Single-Modal Attractor Dynamics

```lean
-- Energy sequence is monotone non-increasing
theorem energy_antitone {F E} [ContF] [ContE] (x0 : State) :
  Antitone (fun k => E (orbit F x0 k))

-- Energy converges to its infimum
theorem energy_convergent {F E} [ContF] [ContE] (x0 : State) :
  Tendsto (fun k => E (orbit F x0 k)) atTop (𝓝 (⨅ k, E (orbit F x0 k)))

-- If orbit converges, limit is a fixed point
theorem fixed_point_of_limit {F E} [ContF] [ContE]
  (x0 : State) (x* : State) (h_lim : Tendsto (orbit F x0) atTop (𝓝 x*)) :
  F x* = x*
```

### Composite.lean — Composite Architecture, Async Updates

```lean
-- Total energy converges under async updates
theorem async_energy_converges {n} {F : State n → State n}
  (hE_bounded : ∀i, 0 ≤ E_i i (X i)))
  (hE_descent : ∀i, E_i i (F_i (X i)) ≤ E_i i (X i))) :
  Tendsto (fun t => E_total (X t)) atTop (𝓝 (⨅ t, E_total (X t)))

-- Robust convergence under bounded noise
theorem robust_async_energy_converges
  (h_noise : Summable (fun k => ‖ε_k‖)) :
  Tendsto (fun t => E_total (X t + ε_t)) atTop (𝓝 (⨅ t, E_total (X t + ε_t)))
```

---

## 🚀 Running the Proofs / 运行证明

```bash
# Install Lean 4 via elan
elan init
elan override leanprover--lean4:4.19.0

# Build (requires ~10 GB RAM + mathlib)
lake build

# Or open in VS Code + Lean 4 extension
code .
```

---

## 🔗 Connection to ASI / 与热力学解析智能的关联

| Lean4 Theorem | Thermodynamic AGI Meaning |
|--------------|--------------------------|
| `energy_convergent` | Free energy F is monotone decreasing → always converges (H1/H2) |
| `fixed_point_of_limit` | Attractor = dynamical fixed point (H2/H3) |
| `composite_energy_converges` | Multiple CLFA systems → total energy converges (H5) |
| `robust_async_energy_converges` | Noisy/distributed MetaGate → still converges (H4) |
| `async_limit_is_fixed` | Async multi-agent limit = consistent state (L4/L5) |

**Physical meaning**: These are not heuristics. They are **theorems**.
If the premises hold (continuous dynamics + bounded energy + monotone descent),
the conclusions **must** follow.

---

## 📚 Key References

| Paper | Link |
|-------|------|
| Landauer 1961 (irreversibility) | https://doi.org/10.1147/rd.53.0163 |
| Hopfield 1982 (energy networks) | https://doi.org/10.1073/pnas.79.8.2554 |
| Friston 2010 (Free Energy Principle) | https://doi.org/10.1038/nrn2787 |
| Full bibliography (ASI repo) | https://github.com/simulai/ASI/blob/main/02_theory/references.md |

---

## ⚖️ License

MIT License — free to use, build on, argue with.
