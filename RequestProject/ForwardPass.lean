/-
# Forward Pass: Sequential and Parallel

This file defines the forward pass of the dual-regularized Riccati recursion,
in both sequential and parallel settings, and proves that the parallel pass
produces the same states/controls/duals as the sequential pass.

## Sequential Forward Pass (Definitions)

Given the backward Riccati solution (Pₖ, pₖ, Kₖ, kₖ), the trajectory
recovery formulas are:
1. x₀ = (I + Δ₀ P₀)⁻¹ (c₀ − Δ₀ p₀)
2. uₖ = Kₖ xₖ + kₖ
3. x_{k+1} = (I + Δ_{k+1} P_{k+1})⁻¹ (Aₖ xₖ + Bₖ uₖ + c_{k+1} − Δ_{k+1} p_{k+1})
4. yₖ = Pₖ xₖ + pₖ

## Parallel Forward Pass (Definitions + Equivalence)

The state transition x_{k+1} = F_k x_k + f_k is affine, where:
  F_k = (I + Δ_{k+1} P_{k+1})⁻¹ (Aₖ + Bₖ Kₖ)
  f_k = (I + Δ_{k+1} P_{k+1})⁻¹ (Bₖ kₖ + c_{k+1} − Δ_{k+1} p_{k+1})

Using the associative affine composition scan from AffineAssoc.lean,
all states can be computed in O(log(N) log(n)) parallel time.

## What is proved

- `seqForwardState_affine`: The sequential step is affine (x_{k+1} = F_k x_k + f_k).
- `parForwardState_eq_seqForwardState`: Parallel states match sequential states.
- `parForwardDual_eq_seqForwardDual`: Parallel duals match sequential duals.
- `parForwardControl_eq_seqForwardControl`: Parallel controls match sequential controls.

## What is NOT proved

- That these formulas actually recover the optimal trajectory (i.e., that the
  trajectory minimizes the dual-regularized Lagrangian). The formulas are defined
  but their optimality is not formally verified.

References:
- Sequential forward pass formulas: `\label{main-seq-theorem}` of the paper
- Parallel forward pass: `\label{composing-affine-functions}` + parallel_calculus.tex
-/
import Mathlib
import RequestProject.DualRegLQR
import RequestProject.SequentialRiccati
import RequestProject.AffineAssoc

open Matrix

set_option maxHeartbeats 1600000

variable {n m : ℕ} [DecidableEq (Fin n)] [DecidableEq (Fin m)]

-- ═══════════════════════════════════════════════════════════════════════════
-- § 1. Sequential Forward Pass Definitions
-- ═══════════════════════════════════════════════════════════════════════════

/-- Per-stage feedback data extracted from the backward Riccati solution.
Contains the gain matrix Kₖ and feedforward vector kₖ. -/
structure RiccatiFeedback (n m : ℕ) where
  /-- Optimal feedback gain: Kₖ = −Gₖ⁻¹ Hₖ -/
  K : Matrix (Fin m) (Fin n) ℝ
  /-- Optimal feedforward: kₖ = −Gₖ⁻¹ hₖ -/
  kvec : Fin m → ℝ

/-- Extract the per-stage feedback from the backward Riccati solution.

Given Pₖ₊₁, pₖ₊₁ from the backward pass and stage data, compute:
- Wₖ₊₁ = Pₖ₊₁ (I + Δₖ₊₁ Pₖ₊₁)⁻¹
- Gₖ = Rₖ + Bₖᵀ Wₖ₊₁ Bₖ
- Hₖ = Bₖᵀ Wₖ₊₁ Aₖ + Mₖᵀ
- hₖ = rₖ + Bₖᵀ gₖ₊₁  where  gₖ₊₁ = (I + Pₖ₊₁Δₖ₊₁)⁻¹pₖ₊₁ + Wₖ₊₁cₖ₊₁
- Kₖ = −Gₖ⁻¹ Hₖ
- kₖ = −Gₖ⁻¹ hₖ -/
noncomputable def extractFeedback
    (Pk1 : Matrix (Fin n) (Fin n) ℝ) (pk1 : Fin n → ℝ)
    (Δk1 : Matrix (Fin n) (Fin n) ℝ) (ck1 : Fin n → ℝ)
    (Rk : Matrix (Fin m) (Fin m) ℝ) (Mk : Matrix (Fin n) (Fin m) ℝ)
    (Ak : Matrix (Fin n) (Fin n) ℝ) (Bk : Matrix (Fin n) (Fin m) ℝ)
    (rk : Fin m → ℝ) : RiccatiFeedback n m :=
  let W := riccatiW Pk1 Δk1
  let ψ := ((1 + Pk1 * Δk1)⁻¹).mulVec pk1
  let g := ψ + W.mulVec ck1
  let G := riccatiG Rk Bk W
  let H := riccatiH Mk Ak Bk W
  let hh := rk + (Bk.transpose).mulVec g
  { K := riccatiK G H
    kvec := -(G⁻¹).mulVec hh }

/-- Extract feedback for stage k of a DualRegLQR problem, using
the backward Riccati solution. -/
noncomputable def DualRegLQR.feedback {N : ℕ}
    (prob : DualRegLQR n m N) (k : Fin N) : RiccatiFeedback n m :=
  let idx_back := N - 1 - k.val  -- backward index for P_{k+1}
  let Pk1 := backwardP prob idx_back
  let pk1 := backwardp prob idx_back
  let Δk1 := prob.Delta ⟨k.val + 1, by omega⟩
  let ck1 := prob.cvec ⟨k.val + 1, by omega⟩
  extractFeedback Pk1 pk1 Δk1 ck1 (prob.R k) (prob.Mcross k)
    (prob.A k) (prob.B k) (prob.rvec k)

/-- Sequential forward pass: compute the optimal state trajectory.

`seqForwardState prob i` returns xₖ for k = i, starting from x₀.

- `seqForwardState prob 0` = x₀ = (I + Δ₀ P₀)⁻¹ (c₀ − Δ₀ p₀)
- `seqForwardState prob (k+1)` = (I + Δₖ₊₁ Pₖ₊₁)⁻¹ (Aₖ xₖ + Bₖ uₖ + cₖ₊₁ − Δₖ₊₁ pₖ₊₁)

where uₖ = Kₖ xₖ + kₖ. -/
noncomputable def seqForwardState {N : ℕ}
    (prob : DualRegLQR n m N) : ℕ → (Fin n → ℝ)
  | 0 =>
    let P0 := backwardP prob N
    let p0 := backwardp prob N
    let Δ0 := prob.Delta ⟨0, by omega⟩
    let c0 := prob.cvec ⟨0, by omega⟩
    optimalInitialState P0 p0 Δ0 c0
  | k + 1 =>
    if h : k < N then
      let xk := seqForwardState prob k
      let fb := prob.feedback ⟨k, h⟩
      let uk := fb.K.mulVec xk + fb.kvec
      let Pk1 := backwardP prob (N - 1 - k)
      let pk1 := backwardp prob (N - 1 - k)
      let Δk1 := prob.Delta ⟨k + 1, by omega⟩
      let ck1 := prob.cvec ⟨k + 1, by omega⟩
      optimalNextState Pk1 pk1 Δk1 ck1 (prob.A ⟨k, h⟩) (prob.B ⟨k, h⟩) xk uk
    else seqForwardState prob k

/-- Sequential forward pass: compute the optimal control at stage k.
uₖ = Kₖ xₖ + kₖ -/
noncomputable def seqForwardControl {N : ℕ}
    (prob : DualRegLQR n m N) (k : Fin N) : Fin m → ℝ :=
  let xk := seqForwardState prob k.val
  let fb := prob.feedback k
  fb.K.mulVec xk + fb.kvec

/-- Sequential forward pass: recover the optimal dual variable.
yₖ = Pₖ xₖ + pₖ -/
noncomputable def seqForwardDual {N : ℕ}
    (prob : DualRegLQR n m N) (k : Fin (N + 1)) : Fin n → ℝ :=
  let i := N - k.val  -- backward index
  let Pk := backwardP prob i
  let pk := backwardp prob i
  let xk := seqForwardState prob k.val
  optimalDual Pk pk xk

-- ═══════════════════════════════════════════════════════════════════════════
-- § 2. Parallel Forward Pass: Affine Transition Functions
-- ═══════════════════════════════════════════════════════════════════════════

/-- The state transition at stage k is an affine function:
    x_{k+1} = F_k x_k + f_k

where:
  F_k = (I + Δ_{k+1} P_{k+1})⁻¹ (A_k + B_k K_k)
  f_k = (I + Δ_{k+1} P_{k+1})⁻¹ (B_k k_k + c_{k+1} − Δ_{k+1} p_{k+1})

This is the affine map that, when composed via an associative scan,
enables the parallel forward pass. -/
noncomputable def forwardAffineMap {N : ℕ}
    (prob : DualRegLQR n m N) (k : Fin N)
    : (Fin n → ℝ) × Matrix (Fin n) (Fin n) ℝ :=
  let fb := prob.feedback k
  let Pk1 := backwardP prob (N - 1 - k.val)
  let pk1 := backwardp prob (N - 1 - k.val)
  let Δk1 := prob.Delta ⟨k.val + 1, by omega⟩
  let ck1 := prob.cvec ⟨k.val + 1, by omega⟩
  let Ak := prob.A k
  let Bk := prob.B k
  let inv := (1 + Δk1 * Pk1)⁻¹
  -- f_k = inv · (B_k k_k + c_{k+1} − Δ_{k+1} p_{k+1})
  let fk := inv.mulVec (Bk.mulVec fb.kvec + ck1 - Δk1.mulVec pk1)
  -- F_k = inv · (A_k + B_k K_k)
  let Fk := inv * (Ak + Bk * fb.K)
  (fk, Fk)

-- ═══════════════════════════════════════════════════════════════════════════
-- § 3. Parallel Forward Pass: Composed Affine Maps via Scan
-- ═══════════════════════════════════════════════════════════════════════════

/-- Left-fold of affine compositions: computes F_{k-1} ∘ ··· ∘ F_0
as an element of (offset, matrix).

`affineFoldLeft maps i` = the composition of the first `i` affine maps.
- `affineFoldLeft maps 0` = (0, I)  (identity function)
- `affineFoldLeft maps (i+1)` = affineCompose (affineFoldLeft maps i) (maps i)

The resulting pair (a, B) represents x ↦ B x + a. -/
noncomputable def affineFoldLeft
    (maps : ℕ → (Fin n → ℝ) × Matrix (Fin n) (Fin n) ℝ)
    : ℕ → (Fin n → ℝ) × Matrix (Fin n) (Fin n) ℝ
  | 0 => (0, 1)  -- identity affine map
  | i + 1 => affineCompose (affineFoldLeft maps i) (maps i)

/-- The parallel forward pass computes all states simultaneously:
  xₖ = (composed affine map up to k) applied to x₀.

`parForwardState prob k` returns the same xₖ as the sequential forward pass,
but the composed maps can be computed in O(log N) parallel time using an
associative scan (by `affineCompose_assoc`).

Note: We require k ≤ N. For k within range, the affine maps are well-defined. -/
noncomputable def parForwardState {N : ℕ}
    (prob : DualRegLQR n m N) (k : Fin (N + 1)) : Fin n → ℝ :=
  let x0 := seqForwardState prob 0
  let maps : ℕ → (Fin n → ℝ) × Matrix (Fin n) (Fin n) ℝ :=
    fun i => if h : i < N then forwardAffineMap prob ⟨i, h⟩ else (0, 1)
  let composed := affineFoldLeft maps k.val
  composed.2.mulVec x0 + composed.1

/-
═══════════════════════════════════════════════════════════════════════════
§ 4. Sequential Forward State = Affine Propagation
═══════════════════════════════════════════════════════════════════════════

The sequential forward state transition is an affine function of xₖ.
This theorem shows that:

  x_{k+1} = F_k · x_k + f_k

where (f_k, F_k) = forwardAffineMap prob k.

This is the key observation enabling parallelization: the sequential
recurrence x_{k+1} = φ(x_k) has the affine structure needed for
an associative scan.
-/
theorem seqForwardState_affine {N : ℕ}
    (prob : DualRegLQR n m N) (k : Fin N) :
    seqForwardState prob (k.val + 1) =
    let aff := forwardAffineMap prob k
    aff.2.mulVec (seqForwardState prob k.val) + aff.1 := by
  rw [ seqForwardState ];
  unfold forwardAffineMap optimalNextState
  -- Matrix.add_mulVec is needed by the chained `ext i; simp` for the second goal
  set_option linter.unusedSimpArgs false in
  simp +decide [ Matrix.mulVec_add, Matrix.add_mulVec ] ; ring;
  ext i; simp +decide [ Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.add_mulVec, Matrix.mul_add, add_assoc ]

/-
═══════════════════════════════════════════════════════════════════════════
§ 5. Parallel Forward State Matches Sequential
═══════════════════════════════════════════════════════════════════════════

The parallel forward pass produces the same states as the sequential
forward pass. This is proved by induction using `seqForwardState_affine`
and the definition of `affineFoldLeft`.

The significance of this theorem is that `parForwardState` can be computed
in O(log N) parallel time using an associative scan on affine compositions
(by `affineCompose_assoc`), while `seqForwardState` requires O(N) sequential
steps.
-/
theorem parForwardState_eq_seqForwardState {N : ℕ}
    (prob : DualRegLQR n m N) (k : Fin (N + 1)) :
    parForwardState prob k = seqForwardState prob k.val := by
  have h_ind : ∀ (k : ℕ) (hk : k ≤ N), seqForwardState prob k = let x0 := seqForwardState prob 0; let maps : ℕ → (Fin n → ℝ) × Matrix (Fin n) (Fin n) ℝ := fun i => if h : i < N then forwardAffineMap prob ⟨i, h⟩ else (0, 1); let composed := affineFoldLeft maps k; composed.2.mulVec x0 + composed.1 := by
    intro k hk; induction' k with k ih <;> simp_all +decide [] ;
    · unfold affineFoldLeft; aesop;
    · convert seqForwardState_affine prob ⟨ k, hk ⟩ using 1;
      simp +decide [ affineFoldLeft, affineCompose ];
      simp +decide [ hk, ih hk.le, Matrix.mulVec_add, Matrix.mulVec_mulVec ];
      abel1;
  exact h_ind k ( Fin.is_le k ) ▸ rfl

-- ═══════════════════════════════════════════════════════════════════════════
-- § 6. Dual and Control Recovery from Parallel States
-- ═══════════════════════════════════════════════════════════════════════════

/-- Once all states xₖ are computed (in parallel), the dual variables
yₖ = Pₖ xₖ + pₖ can be recovered independently (O(1) w.r.t. N).

This is the same as seqForwardDual, but using parForwardState. -/
noncomputable def parForwardDual {N : ℕ}
    (prob : DualRegLQR n m N) (k : Fin (N + 1)) : Fin n → ℝ :=
  let i := N - k.val
  let Pk := backwardP prob i
  let pk := backwardp prob i
  let xk := parForwardState prob k
  optimalDual Pk pk xk

/-- Once all states xₖ are computed (in parallel), the controls
uₖ = Kₖ xₖ + kₖ can also be recovered independently (O(1) w.r.t. N). -/
noncomputable def parForwardControl {N : ℕ}
    (prob : DualRegLQR n m N) (k : Fin N) : Fin m → ℝ :=
  let xk := parForwardState prob ⟨k.val, by omega⟩
  let fb := prob.feedback k
  fb.K.mulVec xk + fb.kvec

/-- The parallel dual recovery matches the sequential one (given matching states). -/
theorem parForwardDual_eq_seqForwardDual {N : ℕ}
    (prob : DualRegLQR n m N) (k : Fin (N + 1)) :
    parForwardDual prob k = seqForwardDual prob k := by
  unfold parForwardDual seqForwardDual optimalDual
  simp only
  have h := parForwardState_eq_seqForwardState prob k
  rw [h]

/-- The parallel control recovery matches the sequential one. -/
theorem parForwardControl_eq_seqForwardControl {N : ℕ}
    (prob : DualRegLQR n m N) (k : Fin N) :
    parForwardControl prob k = seqForwardControl prob k := by
  unfold parForwardControl seqForwardControl
  simp only
  have h := parForwardState_eq_seqForwardState prob ⟨k.val, by omega⟩
  rw [h]

-- ═══════════════════════════════════════════════════════════════════════════
-- § 7. Complexity Summary (Informal)
-- ═══════════════════════════════════════════════════════════════════════════

/-!
### Parallel Time Complexity

The combined parallel time complexity of the dual-regularized Riccati method is:

1. **Backward pass** (parallel IVF scan): O(log(N) · log(n)²)
   - Compute base-case IVFs: O(log(m)² + log(n)²) per stage, O(1) w.r.t. N
   - Reverse associative scan on IVF combination: O(log(N)) scan steps,
     each requiring O(log(n)²) for matrix inversions and multiplications

2. **Forward pass** (parallel affine scan): O(log(N) · log(n))
   - Compute x₀: O(log(n)²) for matrix inversion
   - Compute per-stage affine maps (F_k, f_k): O(log(m)² + log(n)²), O(1) w.r.t. N
   - Forward associative scan on affine compositions: O(log(N) · log(n))
   - Recover all xₖ from composed maps: O(log(n)), O(1) w.r.t. N
   - Recover all uₖ = Kₖ xₖ + kₖ: O(log(m) + log(n)), O(1) w.r.t. N
   - Recover all yₖ = Pₖ xₖ + pₖ: O(log(n)), O(1) w.r.t. N

Total: O(log(m)² + log(N) · log(n)²)
-/