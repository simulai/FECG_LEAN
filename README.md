# FECG_LEAN: Formalized Energy-Based Concept Generation
# 热力学吸引子动力学的 Lean4 形式化证明

[![License: MIT](https://img.shields.io/badge/License-MIT-blue.svg)](https://opensource.org/licenses/MIT)
[![Lean 4](https://img.shields.io/badge/Lean-4-8957e5?style=flat)](https://leanprover.github.io)
[![Mathlib](https://img.shields.io/badge/Mathlib-latest-ea8805?style=flat)](https://github.com/leanprover-community/mathlib4)

> **Part of the [Epistemic Axiomatic System (EAS)](https://github.com/simulai/EAS-ML-Foundation)**
>
> This repo provides the **dynamical systems proof layer**: within the epistemic bounds defined by EAS, attention dynamics provably converge to attractors.

---

## 📖 Overview

| EN | ZH |
|----|----|
| Every intelligent system minimizes free energy — this is a **physical law**, not a metaphor. | 任何智能系统都在最小化自由能——这是**物理定律**，不是比喻。 |
| FECG_LEAN proves this mathematically: energy bounded + monotone decreasing → attractor exists. | FECG_LEAN 用数学证明：能量有下界 + 单调不增 → 吸引子存在。 |
| Softmax attention = Gibbs distribution = Helmholtz free energy minimization. | Softmax 注意力 = Gibbs 分布 = Helmholtz 自由能最小化。 |

---

## 📁 Lean 4 Source Files

| File | Key Definitions & Theorems | Status |
|------|---------------------------|--------|
| **`FECG_LEAN.lean`** | `energy_antitone`, `energy_convergent`, `fixed_point_of_limit` | ✅ Complete |
| **`Composite.lean`** | `composite_energy_converges`, `async_energy_converges`, `robust_async_energy_converges` | ✅ Complete |
| **`MultiModal.lean`** | `joint_energy_converges`, `attractor_exists_on_compact`, `lasalle_stability` | ✅ Complete |
| **`AttnEnergy.lean`** | `two_token_attention_contract` — attention distance contraction | ✅ Complete |
| **`NTokenAttn.lean`** | n-token Lyapunov dynamics, contraction factor independent of n | 🔄 In progress |
| **`BasinIntegration.lean`** | KL divergence ↔ geometric proximity in Gaussian basins | 🔄 In progress |
| **`HelmholtzAttention.lean`** | `helmholtz_identity`, `softmax_as_gibbs`, `attention_free_energy_min`, `landauer_bound` | ✅ Complete |
| **`ScaleOperator.lean`** | Micro-macro bridge operator S, topological invariance + energy decrease | ✅ Complete |

---

## 🔬 Core Theorems

### Attractor Dynamics (FECG_LEAN.lean)
- Energy sequence is monotone non-increasing → converges to infimum
- If orbit converges, limit is a fixed point

### Thermodynamic Attention (HelmholtzAttention.lean)
- **F = ⟨E⟩ − (1/β)·S** — Helmholtz free energy identity for attention
- Softmax = Gibbs distribution → attention minimizes free energy
- Zero-temperature limit: attention → argmin energy (greedy)
- Landauer bound: minimum computational dissipation

### Scale Operator (ScaleOperator.lean)
- Bridge operator $\mathcal{S}$ maps micro-dynamics to macro-dynamics
- Preserves topological invariants + free energy decrease
- Micro → macro convergence theorem

### Attention Contraction (AttnEnergy + NTokenAttn)
- Two-token: distance contracts by factor $(1 - 2\alpha)$ per step
- N-token: contraction factor independent of token count $n$
- Geometric convergence to attractor

---

## 🚀 Running the Proofs

```bash
# Install Lean 4
curl -sSL https://github.com/leanprover/elan/releases/latest/download/elan-init.sh | sh

# Clone and build
git clone https://github.com/simulai/FECG_LEAN.git
cd FECG_LEAN
lake build
```

---

## 📐 Relationship to EAS

| Layer | Repo | What it proves |
|-------|------|----------------|
| **Epistemic bounds** | [EAS-ML-Foundation](https://github.com/simulai/EAS-ML-Foundation) | $S \subset E \implies R_S \not\cong E$ — perfect self-modeling impossible |
| **Dynamical convergence** | **FECG_LEAN** (this repo) | Attention dynamics provably converge within epistemic bounds |

EAS defines **what cognition cannot do**. FECG_LEAN proves **what attention dynamics do within those bounds**.

---

## Author

**Jing Zhang** — Independent Researcher  
ORCID: [0009-0008-3136-2457](https://orcid.org/0009-0008-3136-2457)  
GitHub: [@simulai](https://github.com/simulai)
