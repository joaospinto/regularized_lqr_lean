/-
# Dual-Regularized LQR: Problem Definition and PSD Theorem

This file defines the dual-regularized LQR problem from
"Dual-Regularized Riccati Recursions for Interior-Point Optimal Control"
(Sousa-Pinto & Orban), and proves that the cost-to-go Hessian Pₖ is PSD.

We explicitly define:
1. The dual-regularized LQR problem (all matrices, vectors, constants)
2. The cost-to-go value functions Vₖ(x) = ½ xᵀ Pₖ x + pₖᵀ x + constₖ
3. The backward Riccati recursion with explicit formulas for every component
   (Pₖ, pₖ, constₖ), including the constant terms (skipped in the paper)
4. All intermediate Riccati quantities (Wₖ₊₁, ψₖ₊₁, gₖ₊₁, Gₖ, Hₖ, hₖ, Kₖ, kₖ)
5. The optimal control law uₖ = Kₖ xₖ + kₖ
6. The optimal state/dual variable recovery formulas

The main proved result (`backwardP_posSemidef`) is that Pₖ is positive
semidefinite for all k ∈ {0,…,N}. This is part of the sequential Riccati
theorem `\label{main-seq-theorem}` of the paper.

Proved in SequentialRiccati.lean (§ 3):
- The Riccati optimal (u*, x'*, y*) satisfy the first-order optimality
  (KKT/gradient) conditions of the one-step Lagrangian.
- (u*, x'*) minimizes the Lagrangian for fixed y = y* (primal completing
  the square), proving the control law u* = Kx + k is optimal.
- y* maximizes the Lagrangian for fixed (u*, x'*) (dual completing
  the square), proving the dual recovery y* = Px + p is optimal.

Fully proved:
- The saddle-point value L(x, u*, x'*, y*) equals the Riccati cost-to-go
  V_k(x) = ½ xᵀ P_k x + p_kᵀ x + const_k (value_identity_step2 and value_identity).
-/
import Mathlib
import RequestProject.SequentialRiccati

open Matrix

set_option maxHeartbeats 800000

variable {n m : ℕ} [DecidableEq (Fin n)] [DecidableEq (Fin m)]

-- ═══════════════════════════════════════════════════════════════════════════
-- § 1. Dual-Regularized LQR Problem Data
-- ═══════════════════════════════════════════════════════════════════════════

/-- Complete input data for a dual-regularized LQR problem with `N` stages,
    `n`-dimensional state, and `m`-dimensional control.

The dual-regularized Lagrangian is:

```
  R(x₀, u₀, …, xₙ, y₀, …, yₙ) =
    Σᵢ₌₀ᴺ⁻¹ (½ xᵢᵀ Qᵢ xᵢ + xᵢᵀ Mᵢ uᵢ + ½ uᵢᵀ Rᵢ uᵢ + qᵢᵀ xᵢ + rᵢᵀ uᵢ)
    + ½ xₙᵀ Qₙ xₙ + qₙᵀ xₙ
    + y₀ᵀ (c₀ − x₀)
    + Σᵢ₌₀ᴺ⁻¹ yᵢ₊₁ᵀ (Aᵢ xᵢ + Bᵢ uᵢ + cᵢ₊₁ − xᵢ₊₁)
    − Σᵢ₌₀ᴺ ½ yᵢᵀ Δᵢ yᵢ
```

The problem is: `max_{y₀,…,yₙ} min_{x₀,u₀,…,xₙ} R(x, u, y)`. -/
structure DualRegLQR (n m N : ℕ) where
  /-- State cost Hessians `Qₖ` (`n × n`, symmetric PSD), `k = 0, …, N` -/
  Q : Fin (N + 1) → Matrix (Fin n) (Fin n) ℝ
  /-- Control cost Hessians `Rₖ` (`m × m`, symmetric PD), `k = 0, …, N − 1` -/
  R : Fin N → Matrix (Fin m) (Fin m) ℝ
  /-- State-control cross-cost matrices `Mₖ` (`n × m`), `k = 0, …, N − 1` -/
  Mcross : Fin N → Matrix (Fin n) (Fin m) ℝ
  /-- Dynamics state matrices `Aₖ` (`n × n`), `k = 0, …, N − 1` -/
  A : Fin N → Matrix (Fin n) (Fin n) ℝ
  /-- Dynamics control matrices `Bₖ` (`n × m`), `k = 0, …, N − 1` -/
  B : Fin N → Matrix (Fin n) (Fin m) ℝ
  /-- Dual regularization matrices `Δₖ` (`n × n`, symmetric PD), `k = 0, …, N` -/
  Delta : Fin (N + 1) → Matrix (Fin n) (Fin n) ℝ
  /-- State cost linear terms `qₖ` (`n`-vector), `k = 0, …, N` -/
  qvec : Fin (N + 1) → (Fin n → ℝ)
  /-- Control cost linear terms `rₖ` (`m`-vector), `k = 0, …, N − 1` -/
  rvec : Fin N → (Fin m → ℝ)
  /-- Constraint affine terms `cₖ` (`n`-vector), `k = 0, …, N`.
      `c₀` encodes the initial state constraint; `cₖ₊₁` the dynamics offset. -/
  cvec : Fin (N + 1) → (Fin n → ℝ)

-- ═══════════════════════════════════════════════════════════════════════════
-- § 2. Cost-to-Go Value Function
-- ═══════════════════════════════════════════════════════════════════════════

/-- Components of the cost-to-go value function at stage `k`:

```
    Vₖ(x) = ½ xᵀ Pₖ x + pₖᵀ x + constₖ
```

- `P` : Hessian of `Vₖ` (`n × n`, symmetric PSD by the main theorem)
- `p` : linear coefficient (`n`-vector, equals `∇Vₖ(0)`)
- `constTerm` : constant term (scalar, equals `Vₖ(0)`) -/
structure CostToGo (n : ℕ) where
  /-- Hessian of the value function (`n × n`, symmetric PSD) -/
  P : Matrix (Fin n) (Fin n) ℝ
  /-- Linear coefficient of the value function (`n`-vector) -/
  p : Fin n → ℝ
  /-- Constant term of the value function (scalar) -/
  constTerm : ℝ

/-- Evaluate the cost-to-go: `Vₖ(x) = ½ xᵀ Pₖ x + pₖᵀ x + constₖ` -/
noncomputable def CostToGo.eval (V : CostToGo n) (x : Fin n → ℝ) : ℝ :=
  (1 / 2 : ℝ) * (x ⬝ᵥ V.P.mulVec x) + V.p ⬝ᵥ x + V.constTerm

-- ═══════════════════════════════════════════════════════════════════════════
-- § 3. Conversion to LQRStage Format (for PSD proof)
-- ═══════════════════════════════════════════════════════════════════════════

/-- Convert `DualRegLQR` problem data to the `LQRStage` format.
    Stage `i` maps to `LQRStage` with `Δ_next = Δᵢ₊₁`. -/
noncomputable def DualRegLQR.toLQRStages {N : ℕ}
    (prob : DualRegLQR n m N) : Fin N → LQRStage n m :=
  fun i => {
    Q := prob.Q ⟨i.val, by omega⟩
    R := prob.R i
    S := prob.Mcross i
    A := prob.A i
    B := prob.B i
    Δ_next := prob.Delta ⟨i.val + 1, by omega⟩
  }

-- ═══════════════════════════════════════════════════════════════════════════
-- § 4. Backward Riccati Recursion: All Three Components
-- ═══════════════════════════════════════════════════════════════════════════

/-! ### Component 1: Hessian `Pₖ`

The Hessian recursion is defined via `riccatiBackward` from
`RiccatiRecursion.lean`. Expanding the definitions:

**Base case** (`k = N`): `Pₙ = Qₙ`

**Recursive step** (from `Pₖ₊₁` to `Pₖ`):

1. Smoothed Hessian: `Wₖ₊₁ = Pₖ₊₁ (I + Δₖ₊₁ Pₖ₊₁)⁻¹`
2. Effective control Hessian: `Gₖ = Rₖ + Bₖᵀ Wₖ₊₁ Bₖ`
3. Cross Hessian: `Hₖ = Bₖᵀ Wₖ₊₁ Aₖ + Mₖᵀ`
4. Optimal feedback gain: `Kₖ = −Gₖ⁻¹ Hₖ`
5. Hessian update: `Pₖ = Qₖ + Aₖᵀ Wₖ₊₁ Aₖ + Hₖᵀ Kₖ` -/

/-- The Hessian `Pₖ` of the cost-to-go, computed by the backward Riccati recursion.
    `backwardP prob i` returns `P` at stage `N − i`. -/
noncomputable def backwardP {N : ℕ}
    (prob : DualRegLQR n m N) (i : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  riccatiBackward (prob.toLQRStages) (prob.Q ⟨N, by omega⟩) i

/-! ### Component 2: Linear coefficient `pₖ`

**Base case** (`k = N`): `pₙ = qₙ`

**Recursive step** (from `pₖ₊₁` to `pₖ`):

1. Regularized linear term: `ψₖ₊₁ = (I + Pₖ₊₁ Δₖ₊₁)⁻¹ pₖ₊₁`
2. Combined gradient: `gₖ₊₁ = ψₖ₊₁ + Wₖ₊₁ cₖ₊₁`
3. Control gradient: `hₖ = rₖ + Bₖᵀ gₖ₊₁`
4. Optimal feedforward: `kₖ = −Gₖ⁻¹ hₖ`
5. Linear update: `pₖ = qₖ + Aₖᵀ gₖ₊₁ + Hₖᵀ kₖ`

(Corollary `\label{p-recurrence}` of the paper shows this satisfies the affine
recurrence `pₖ = qₖ + Kₖᵀ rₖ + (Aₖ + Bₖ Kₖ)ᵀ gₖ₊₁`.) -/

/-- The linear coefficient `pₖ` of the cost-to-go.
    `backwardp prob i` returns `p` at stage `N − i`. -/
noncomputable def backwardp {N : ℕ}
    (prob : DualRegLQR n m N) : ℕ → (Fin n → ℝ)
  | 0 => prob.qvec ⟨N, by omega⟩
  | i + 1 =>
    if h : i < N then
      let idx : Fin N := ⟨N - 1 - i, by omega⟩
      -- Previous-stage value function components
      let Pk1 := backwardP prob i           -- Pₖ₊₁
      let pk1 := backwardp prob i           -- pₖ₊₁
      -- Stage k+1 regularization and dynamics offset
      let Δk1 := prob.Delta ⟨idx.val + 1, by omega⟩  -- Δₖ₊₁
      let ck1 := prob.cvec ⟨idx.val + 1, by omega⟩   -- cₖ₊₁
      -- Stage k data
      let Rk := prob.R idx                  -- Rₖ
      let Mk := prob.Mcross idx             -- Mₖ
      let Ak := prob.A idx                  -- Aₖ
      let Bk := prob.B idx                  -- Bₖ
      let rk := prob.rvec idx               -- rₖ
      let qk := prob.qvec ⟨idx.val, by omega⟩  -- qₖ
      -- Intermediate: Wₖ₊₁ = Pₖ₊₁ (I + Δₖ₊₁ Pₖ₊₁)⁻¹
      let W := riccatiW Pk1 Δk1
      -- Intermediate: ψₖ₊₁ = (I + Pₖ₊₁ Δₖ₊₁)⁻¹ pₖ₊₁
      let ψ := ((1 + Pk1 * Δk1)⁻¹).mulVec pk1
      -- Intermediate: gₖ₊₁ = ψₖ₊₁ + Wₖ₊₁ cₖ₊₁
      let g := ψ + W.mulVec ck1
      -- Intermediate: Hₖ = Bₖᵀ Wₖ₊₁ Aₖ + Mₖᵀ
      let H := riccatiH Mk Ak Bk W
      -- Intermediate: Gₖ = Rₖ + Bₖᵀ Wₖ₊₁ Bₖ
      let G := riccatiG Rk Bk W
      -- Intermediate: hₖ = rₖ + Bₖᵀ gₖ₊₁
      let hh := rk + (Bk.transpose).mulVec g
      -- Intermediate: kₖ = −Gₖ⁻¹ hₖ
      let kk := -(G⁻¹).mulVec hh
      -- pₖ = qₖ + Aₖᵀ gₖ₊₁ + Hₖᵀ kₖ
      qk + (Ak.transpose).mulVec g + (H.transpose).mulVec kk
    else backwardp prob i

/-! ### Component 3: Constant term `constₖ`

**Base case** (`k = N`): `constₙ = 0`

**Recursive step** (from `constₖ₊₁` to `constₖ`).
This formula is omitted in the paper; we derive it by tracking the
"additive constant" terms discarded during successive variable elimination:

```
  constₖ = constₖ₊₁ + ½ cₖ₊₁ᵀ Wₖ₊₁ cₖ₊₁ + ψₖ₊₁ᵀ cₖ₊₁ − ½ ψₖ₊₁ᵀ Δₖ₊₁ pₖ₊₁ + ½ hₖᵀ kₖ
```

The terms arise from:
- `½ cₖ₊₁ᵀ Wₖ₊₁ cₖ₊₁` — quadratic in dynamics offset from `xₖ₊₁` elimination
- `ψₖ₊₁ᵀ cₖ₊₁` — cross-term between regularized gradient and dynamics offset
- `−½ ψₖ₊₁ᵀ Δₖ₊₁ pₖ₊₁` — cost of dual regularization at the optimum
- `½ hₖᵀ kₖ = −½ hₖᵀ Gₖ⁻¹ hₖ` — optimal value of control quadratic -/

/-- The constant term `constₖ` of the cost-to-go.
    `backwardConst prob i` returns `const` at stage `N − i`. -/
noncomputable def backwardConst {N : ℕ}
    (prob : DualRegLQR n m N) : ℕ → ℝ
  | 0 => 0
  | i + 1 =>
    if h : i < N then
      let idx : Fin N := ⟨N - 1 - i, by omega⟩
      let Pk1 := backwardP prob i
      let pk1 := backwardp prob i
      let Δk1 := prob.Delta ⟨idx.val + 1, by omega⟩
      let ck1 := prob.cvec ⟨idx.val + 1, by omega⟩
      let Rk := prob.R idx
      let Bk := prob.B idx
      let rk := prob.rvec idx
      -- Wₖ₊₁ = Pₖ₊₁ (I + Δₖ₊₁ Pₖ₊₁)⁻¹
      let W := riccatiW Pk1 Δk1
      -- ψₖ₊₁ = (I + Pₖ₊₁ Δₖ₊₁)⁻¹ pₖ₊₁
      let ψ := ((1 + Pk1 * Δk1)⁻¹).mulVec pk1
      -- gₖ₊₁ = ψₖ₊₁ + Wₖ₊₁ cₖ₊₁
      let g := ψ + W.mulVec ck1
      -- Gₖ = Rₖ + Bₖᵀ Wₖ₊₁ Bₖ
      let G := riccatiG Rk Bk W
      -- hₖ = rₖ + Bₖᵀ gₖ₊₁
      let hh := rk + (Bk.transpose).mulVec g
      -- kₖ = −Gₖ⁻¹ hₖ
      let kk := -(G⁻¹).mulVec hh
      -- constₖ = constₖ₊₁ + ½ cᵀWc + ψᵀc − ½ ψᵀΔp + ½ hᵀk
      backwardConst prob i
        + (1 / 2 : ℝ) * (ck1 ⬝ᵥ W.mulVec ck1)
        + (ψ ⬝ᵥ ck1)
        - (1 / 2 : ℝ) * (ψ ⬝ᵥ Δk1.mulVec pk1)
        + (1 / 2 : ℝ) * (hh ⬝ᵥ kk)
    else backwardConst prob i

/-- The full backward Riccati recursion, bundling all components.
    `riccatiBackwardCostToGo prob i` returns `(Pₖ, pₖ, constₖ)` at stage `k = N − i`. -/
noncomputable def riccatiBackwardCostToGo {N : ℕ}
    (prob : DualRegLQR n m N) (i : ℕ) : CostToGo n :=
  { P := backwardP prob i
    p := backwardp prob i
    constTerm := backwardConst prob i }

-- ═══════════════════════════════════════════════════════════════════════════
-- § 5. One-Step Formula (Reference Definition)
-- ═══════════════════════════════════════════════════════════════════════════

/-- One step of the backward Riccati recursion, computing `(Pₖ, pₖ, constₖ)`
from `(Pₖ₊₁, pₖ₊₁, constₖ₊₁)` and stage data. This is a reference definition
that collects all formulas in one place.

### All intermediate quantities

- `Wₖ₊₁ = Pₖ₊₁ (I + Δₖ₊₁ Pₖ₊₁)⁻¹` — smoothed Hessian
- `ψₖ₊₁ = (I + Pₖ₊₁ Δₖ₊₁)⁻¹ pₖ₊₁` — regularized linear term
- `gₖ₊₁ = ψₖ₊₁ + Wₖ₊₁ cₖ₊₁` — combined gradient
- `Gₖ = Rₖ + Bₖᵀ Wₖ₊₁ Bₖ` — effective control Hessian (PD)
- `Hₖ = Bₖᵀ Wₖ₊₁ Aₖ + Mₖᵀ` — cross Hessian
- `hₖ = rₖ + Bₖᵀ gₖ₊₁` — control gradient
- `Kₖ = −Gₖ⁻¹ Hₖ` — optimal feedback gain
- `kₖ = −Gₖ⁻¹ hₖ` — optimal feedforward

### Output formulas

- `Pₖ = Qₖ + Aₖᵀ Wₖ₊₁ Aₖ + Hₖᵀ Kₖ`
- `pₖ = qₖ + Aₖᵀ gₖ₊₁ + Hₖᵀ kₖ`
- `constₖ = constₖ₊₁ + ½ cₖ₊₁ᵀ Wₖ₊₁ cₖ₊₁ + ψₖ₊₁ᵀ cₖ₊₁ − ½ ψₖ₊₁ᵀ Δₖ₊₁ pₖ₊₁ + ½ hₖᵀ kₖ` -/
noncomputable def riccatiOneStep
    (Pk1 : Matrix (Fin n) (Fin n) ℝ) (pk1 : Fin n → ℝ) (constk1 : ℝ)
    (Δk1 : Matrix (Fin n) (Fin n) ℝ) (ck1 : Fin n → ℝ)
    (Qk : Matrix (Fin n) (Fin n) ℝ) (Rk : Matrix (Fin m) (Fin m) ℝ)
    (Mk : Matrix (Fin n) (Fin m) ℝ) (Ak : Matrix (Fin n) (Fin n) ℝ)
    (Bk : Matrix (Fin n) (Fin m) ℝ) (qk : Fin n → ℝ) (rk : Fin m → ℝ)
    : CostToGo n :=
  let W := riccatiW Pk1 Δk1
  let ψ := ((1 + Pk1 * Δk1)⁻¹).mulVec pk1
  let g := ψ + W.mulVec ck1
  let G := riccatiG Rk Bk W
  let H := riccatiH Mk Ak Bk W
  let hh := rk + (Bk.transpose).mulVec g
  let K := riccatiK G H
  let kk := -(G⁻¹).mulVec hh
  { P := riccatiPstep Qk Ak W H K
    p := qk + (Ak.transpose).mulVec g + (H.transpose).mulVec kk
    constTerm := constk1
      + (1 / 2 : ℝ) * (ck1 ⬝ᵥ W.mulVec ck1)
      + (ψ ⬝ᵥ ck1)
      - (1 / 2 : ℝ) * (ψ ⬝ᵥ Δk1.mulVec pk1)
      + (1 / 2 : ℝ) * (hh ⬝ᵥ kk) }

-- ═══════════════════════════════════════════════════════════════════════════
-- § 6. Optimal Solution Recovery
-- ═══════════════════════════════════════════════════════════════════════════

/-- Optimal control: `uₖ = Kₖ xₖ + kₖ`

where `Kₖ = −Gₖ⁻¹ Hₖ` and `kₖ = −Gₖ⁻¹ hₖ`. -/
noncomputable def optimalControl
    (Pk1 : Matrix (Fin n) (Fin n) ℝ) (pk1 : Fin n → ℝ)
    (Δk1 : Matrix (Fin n) (Fin n) ℝ) (ck1 : Fin n → ℝ)
    (Rk : Matrix (Fin m) (Fin m) ℝ)
    (Mk : Matrix (Fin n) (Fin m) ℝ) (Ak : Matrix (Fin n) (Fin n) ℝ)
    (Bk : Matrix (Fin n) (Fin m) ℝ) (rk : Fin m → ℝ)
    (xk : Fin n → ℝ) : Fin m → ℝ :=
  let W := riccatiW Pk1 Δk1
  let ψ := ((1 + Pk1 * Δk1)⁻¹).mulVec pk1
  let g := ψ + W.mulVec ck1
  let G := riccatiG Rk Bk W
  let H := riccatiH Mk Ak Bk W
  let hh := rk + (Bk.transpose).mulVec g
  let K := riccatiK G H
  let kk := -(G⁻¹).mulVec hh
  K.mulVec xk + kk

/-- Optimal initial state: `x₀ = (I + Δ₀ P₀)⁻¹ (c₀ − Δ₀ p₀)`. -/
noncomputable def optimalInitialState
    (P0 : Matrix (Fin n) (Fin n) ℝ) (p0 : Fin n → ℝ)
    (Δ0 : Matrix (Fin n) (Fin n) ℝ) (c0 : Fin n → ℝ)
    : Fin n → ℝ :=
  ((1 + Δ0 * P0)⁻¹).mulVec (c0 - Δ0.mulVec p0)

/-- Optimal next state:
    `xₖ₊₁ = (I + Δₖ₊₁ Pₖ₊₁)⁻¹ (Aₖ xₖ + Bₖ uₖ + cₖ₊₁ − Δₖ₊₁ pₖ₊₁)`. -/
noncomputable def optimalNextState
    (Pk1 : Matrix (Fin n) (Fin n) ℝ) (pk1 : Fin n → ℝ)
    (Δk1 : Matrix (Fin n) (Fin n) ℝ) (ck1 : Fin n → ℝ)
    (Ak : Matrix (Fin n) (Fin n) ℝ) (Bk : Matrix (Fin n) (Fin m) ℝ)
    (xk : Fin n → ℝ) (uk : Fin m → ℝ)
    : Fin n → ℝ :=
  ((1 + Δk1 * Pk1)⁻¹).mulVec
    (Ak.mulVec xk + Bk.mulVec uk + ck1 - Δk1.mulVec pk1)

/-- Optimal dual variable: `yₖ = Pₖ xₖ + pₖ`. -/
noncomputable def optimalDual
    (Pk : Matrix (Fin n) (Fin n) ℝ) (pk : Fin n → ℝ) (xk : Fin n → ℝ)
    : Fin n → ℝ :=
  Pk.mulVec xk + pk

-- ═══════════════════════════════════════════════════════════════════════════
-- § 7. Main Theorem: PSD Preservation
-- ═══════════════════════════════════════════════════════════════════════════

/-- **PSD preservation** (part of `\label{main-seq-theorem}`): the backward
Riccati recursion preserves positive semidefiniteness of the cost-to-go Hessian.

For a dual-regularized LQR problem with `N` stages, if:
- The terminal cost Hessian `Qₙ` is PSD
- At each backward step `i` (computing `Vₖ` from `Vₖ₊₁` where `k = N − 1 − i`),
  the `LQRStageValid` conditions hold for the corresponding stage data

Then `Pₖ` is positive semidefinite for all `k ∈ {0, …, N}`.

The `LQRStageValid` conditions at backward step `i` require:
- The stage cost `[Qₖ, Mₖ; Mₖᵀ, Rₖ]` is jointly PSD
- `Qₖ` and `Rₖ` are symmetric
- `Δₖ₊₁` is PSD
- `I + Δₖ₊₁ Pₖ₊₁` and `I + Pₖ₊₁ Δₖ₊₁` are invertible
- `Gₖ = Rₖ + Bₖᵀ Wₖ₊₁ Bₖ` is invertible

The full cost-to-go value function is:
```
  Vₖ(x) = ½ xᵀ Pₖ x + pₖᵀ x + constₖ
```
with `Pₖ` symmetric PSD, `pₖ` from `backwardp`, and `constₖ` from `backwardConst`. -/
theorem backwardP_posSemidef {N : ℕ} (prob : DualRegLQR n m N)
    (hQN : (prob.Q ⟨N, by omega⟩).PosSemidef)
    (hValid : ∀ (i : ℕ) (hi : i < N),
      LQRStageValid
        (prob.toLQRStages ⟨N - 1 - i, by omega⟩)
        (backwardP prob i))
    : ∀ i, i ≤ N → (backwardP prob i).PosSemidef := by
  intro i hi
  unfold backwardP
  exact riccati_backward_posSemidef
    (prob.toLQRStages) (prob.Q ⟨N, by omega⟩) hQN
    (fun j hj => hValid j hj) i hi
