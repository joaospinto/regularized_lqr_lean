/-
# Quadratic Optimization Lemmas (Lemmas 1 & 3 of the paper)

This file contains the two key quadratic optimization results used in the
backward Riccati recursion to eliminate variables.

## § 1. Lemma 1 — Eliminate y (Quadratic Maximization)

If M is symmetric and positive-definite and f(y) = kᵀy − ½ yᵀMy, then
  max_y f(y) = f(M⁻¹k) = ½ ‖k‖²_{M⁻¹}

The optimizer is y* = M⁻¹k, and the critical point equation is ∇f(y) = k − My = 0.

## § 2. Lemma 3 — Eliminate x (Quadratic Minimization with Penalty)

If P is symmetric PSD, M is symmetric PD, and
  f(x) = ½ xᵀPx + pᵀx + ½ ‖c − x‖²_{M⁻¹}

then the minimizer is x* = (I + MP)⁻¹(c − Mp) and the gradient condition at
the minimizer is (P + M⁻¹)x* = M⁻¹c − p.
-/
import Mathlib

open Matrix

variable {n : ℕ} [DecidableEq (Fin n)]

-- ═══════════════════════════════════════════════════════════════════════════
-- § 1. Lemma 1 — Eliminate y (Quadratic Maximization)
-- ═══════════════════════════════════════════════════════════════════════════

/-- The quadratic form f(y) = kᵀy − ½ yᵀMy -/
noncomputable def quadForm (M : Matrix (Fin n) (Fin n) ℝ) (k y : Fin n → ℝ) : ℝ :=
  dotProduct k y - (1/2) * dotProduct y (M.mulVec y)

/-- At y* = M⁻¹k, the value of the quadratic is ½ kᵀ M⁻¹ k.
    This corresponds to Lemma 1 (eliminate-y) of the paper. -/
theorem quadForm_at_optimizer
    (M : Matrix (Fin n) (Fin n) ℝ)
    (k : Fin n → ℝ)
    (hM : IsUnit M)
    (hMsymm : M.IsSymm) :
    quadForm M k (M⁻¹.mulVec k) = (1/2) * dotProduct k (M⁻¹.mulVec k) := by
  simp [quadForm];
  simp_all +decide [ Matrix.isUnit_iff_isUnit_det ];
  norm_num [ Matrix.mulVec, dotProduct_comm ] ; ring;

/-- The gradient condition: at y* = M⁻¹k, k − M y* = 0. -/
theorem gradient_vanishes_at_optimizer
    (M : Matrix (Fin n) (Fin n) ℝ)
    (k : Fin n → ℝ)
    (hM : IsUnit M) :
    k - M.mulVec (M⁻¹.mulVec k) = 0 := by
  cases hM.nonempty_invertible ; aesop

-- ═══════════════════════════════════════════════════════════════════════════
-- § 2. Lemma 3 — Eliminate x (Quadratic Minimization with Penalty)
-- ═══════════════════════════════════════════════════════════════════════════

/-- The quadratic-with-penalty objective:
    f(x) = ½ xᵀPx + pᵀx + ½ (c−x)ᵀ M⁻¹ (c−x) -/
noncomputable def quadPenaltyObj
    (P : Matrix (Fin n) (Fin n) ℝ)
    (Minv : Matrix (Fin n) (Fin n) ℝ)
    (p c x : Fin n → ℝ) : ℝ :=
  (1/2) * dotProduct x (P.mulVec x) + dotProduct p x
  + (1/2) * dotProduct (c - x) (Minv.mulVec (c - x))

/-- dotProduct distributes over subtraction in the first argument -/
theorem dotProduct_sub_left (a b c : Fin n → ℝ) :
    dotProduct (a - b) c = dotProduct a c - dotProduct b c := by
  simp +decide [ sub_mul, dotProduct ]

/-- mulVec distributes over subtraction -/
theorem mulVec_sub_right (A : Matrix (Fin n) (Fin n) ℝ) (a b : Fin n → ℝ) :
    A.mulVec (a - b) = A.mulVec a - A.mulVec b := by
  ext i; simp +decide [ Matrix.mulVec, dotProduct ] ; ring;
  rw [ Finset.sum_sub_distrib ]

/-- The objective can be rewritten as
    f(x) = ½ xᵀ(P + M⁻¹)x + (p − M⁻¹c)ᵀx + ½ cᵀM⁻¹c -/
theorem quadPenaltyObj_expand
    (P Minv : Matrix (Fin n) (Fin n) ℝ)
    (hMinv : Minv.IsSymm)
    (p c x : Fin n → ℝ) :
    quadPenaltyObj P Minv p c x =
    (1/2) * dotProduct x ((P + Minv).mulVec x)
    + dotProduct (p - Minv.mulVec c) x
    + (1/2) * dotProduct c (Minv.mulVec c) := by
  have h_expand : (c - x) ⬝ᵥ (Minv.mulVec (c - x)) = c ⬝ᵥ (Minv.mulVec c) - 2 * x ⬝ᵥ (Minv.mulVec c) + x ⬝ᵥ (Minv.mulVec x) := by
    simp +decide only [mulVec_sub, dotProduct_sub];
    have h_symm : x ⬝ᵥ Minv.mulVec c = c ⬝ᵥ Minv.mulVec x := by
      simp +decide only [dotProduct, mulVec, Finset.mul_sum _ _ _];
      exact Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by rw [ hMinv.apply ] ; ring );
    simpa [ dotProduct_sub, h_symm ] using by ring;
  simp_all +decide [ quadPenaltyObj, Matrix.add_mulVec, Matrix.mulVec_add ];
  norm_num [ dotProduct_comm ] ; ring

/-- The gradient condition: at the minimizer,
    (P + M⁻¹)x* = M⁻¹c − p -/
theorem gradient_condition_eliminate_x
    (P M : Matrix (Fin n) (Fin n) ℝ)
    (p c : Fin n → ℝ)
    (hM : IsUnit M)
    (hIMP : IsUnit (1 + M * P)) :
    (P + M⁻¹).mulVec ((1 + M * P)⁻¹.mulVec (c - M.mulVec p))
    = M⁻¹.mulVec c - p := by
  have h_inv : (P + M⁻¹) * (1 + M * P)⁻¹ = M⁻¹ := by
    cases hM.nonempty_invertible ; cases hIMP.nonempty_invertible ; simp_all +decide [ Matrix.mul_assoc, Matrix.mul_add, add_mul ];
    have h_factor : M⁻¹ * (1 + M * P) * (1 + M * P)⁻¹ = M⁻¹ := by
      simp +decide [ mul_assoc ];
    simp_all +decide [ mul_add, add_mul, mul_assoc ];
    rwa [ add_comm ];
  simp_all +decide [ Matrix.isUnit_iff_isUnit_det ];
  simp +decide [ Matrix.mulVec_sub, hM, isUnit_iff_ne_zero ]
