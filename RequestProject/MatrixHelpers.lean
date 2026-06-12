/-
# Matrix Helper Lemmas

Generic matrix utilities used throughout the project:

§ 1. Real matrix PSD utilities (PosSemidef ↔ symmetry + nonneg quadratic form)
§ 2. Matrix inverse identities (`\label{inverse-helper}` of the paper)

## PSD Utilities

- `posSemidef_of_symm_nonneg`: construct PSD from symmetry + nonneg quadratic form
- `psd_dotProduct_nonneg`: extract nonneg quadratic form from PSD
- `psd_isSymm`: extract symmetry from PSD

## Matrix Inverse Identities (`\label{inverse-helper}`)

If P and M are invertible matrices over a field, then:
  (1) I - (I + M * P)⁻¹ = M * P * (I + M * P)⁻¹ = (I + M * P)⁻¹ * M * P
  (2) (P + M⁻¹)⁻¹ = (I + M * P)⁻¹ * M = M * (I + P * M)⁻¹
  (3) (I + P * M)⁻¹ * P = P * (I + M * P)⁻¹

These are proved as algebraic identities for invertible matrices over a field,
without requiring positive definiteness (which is only needed to guarantee
the invertibility hypotheses).
-/
import Mathlib

open Matrix

variable {n : ℕ} [DecidableEq (Fin n)]

-- ═══════════════════════════════════════════════════════════════════════════
-- § 1. Real Matrix PSD Utilities
-- ═══════════════════════════════════════════════════════════════════════════

omit [DecidableEq (Fin n)] in
/-- For real matrices, PosSemidef follows from symmetry + nonneg quadratic form -/
lemma posSemidef_of_symm_nonneg {M : Matrix (Fin n) (Fin n) ℝ}
    (hs : M.IsSymm)
    (hq : ∀ x : Fin n → ℝ, 0 ≤ x ⬝ᵥ M.mulVec x) : M.PosSemidef := by
  rw [posSemidef_iff_dotProduct_mulVec]
  refine ⟨?_, fun x => ?_⟩
  · show Mᴴ = M; rw [conjTranspose_eq_transpose_of_trivial]; exact hs
  · simp [star]; exact hq x

omit [DecidableEq (Fin n)] in
/-- Extract the nonneg quadratic form from PosSemidef for real matrices -/
lemma psd_dotProduct_nonneg {M : Matrix (Fin n) (Fin n) ℝ}
    (hM : M.PosSemidef) (x : Fin n → ℝ) : 0 ≤ x ⬝ᵥ M.mulVec x := by
  have := hM.re_dotProduct_nonneg x
  simp [RCLike.re_to_real, star] at this
  exact this

omit [DecidableEq (Fin n)] in
/-- Extract IsSymm from PosSemidef for real matrices -/
lemma psd_isSymm {M : Matrix (Fin n) (Fin n) ℝ} (hM : M.PosSemidef) : M.IsSymm := by
  have h := hM.isHermitian
  show Mᵀ = M
  have heq : Mᴴ = Mᵀ := conjTranspose_eq_transpose_of_trivial M
  rw [← heq]; exact h

-- ═══════════════════════════════════════════════════════════════════════════
-- § 2. Matrix Inverse Identities (`\label{inverse-helper}`)
-- ═══════════════════════════════════════════════════════════════════════════

variable {F : Type*} [Field F]

/-
Identity: M * P * (I + M * P)⁻¹ = I - (I + M * P)⁻¹,
    assuming (1 + M * P) is invertible.
-/
theorem mul_mul_nonsing_inv_eq
    (M P : Matrix (Fin n) (Fin n) F)
    (hMP : IsUnit (1 + M * P)) :
    M * P * (1 + M * P)⁻¹ = 1 - (1 + M * P)⁻¹ := by
  have := hMP.invertible;
  funext i j;
  have := congr_fun ( congr_fun ( mul_invOf_self ( 1 + M * P : Matrix ( Fin n ) ( Fin n ) F ) ) i ) j;
  simp_all +decide [ add_mul, Matrix.one_apply, sub_eq_add_neg ];
  linear_combination' this

/-
Identity: (I + M * P)⁻¹ * M * P = I - (I + M * P)⁻¹,
    assuming (1 + M * P) is invertible.
-/
theorem nonsing_inv_mul_mul_eq
    (M P : Matrix (Fin n) (Fin n) F)
    (hMP : IsUnit (1 + M * P)) :
    (1 + M * P)⁻¹ * (M * P) = 1 - (1 + M * P)⁻¹ := by
  cases' hMP.nonempty_invertible with u hu;
  have := u.2;
  simp_all +decide [ mul_add ];
  exact eq_sub_of_add_eq' this

/-
Identity: (P + M⁻¹)⁻¹ = (I + M * P)⁻¹ * M,
    assuming M and (1 + M * P) are invertible.
-/
theorem inv_add_inv_eq_left
    (M P : Matrix (Fin n) (Fin n) F)
    (hM : IsUnit M)
    (hMP : IsUnit (1 + M * P)) :
    (P + M⁻¹)⁻¹ = (1 + M * P)⁻¹ * M := by
  simp_all +decide [ Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero ];
  rw [ Matrix.inv_eq_left_inv ];
  have := nonsing_inv_mul_mul_eq M P ( show IsUnit ( 1 + M * P ) from by exact ( Matrix.isUnit_iff_isUnit_det _ ).mpr ( isUnit_iff_ne_zero.mpr hMP ) ) ; simp_all +decide [ mul_assoc, mul_add ]

/-
Identity: (P + M⁻¹)⁻¹ = M * (I + P * M)⁻¹,
    assuming M and (1 + P * M) are invertible.
-/
theorem inv_add_inv_eq_right
    (M P : Matrix (Fin n) (Fin n) F)
    (hM : IsUnit M)
    (_hPM : IsUnit (1 + P * M)) :
    (P + M⁻¹)⁻¹ = M * (1 + P * M)⁻¹ := by
  have h_rewrite : P + M⁻¹ = (1 + P * M) * M⁻¹ := by
    simp +decide [ add_mul, mul_assoc ];
    cases hM.nonempty_invertible ; simp +decide [ add_comm ];
  simp_all +decide [ Matrix.isUnit_iff_isUnit_det ];
  rw [ Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv ] ; aesop

/-
Identity: (I + P * M)⁻¹ * P = P * (I + M * P)⁻¹,
    assuming (1 + P * M) and (1 + M * P) are invertible.
-/
theorem inv_mul_comm
    (M P : Matrix (Fin n) (Fin n) F)
    (hPM : IsUnit (1 + P * M))
    (hMP : IsUnit (1 + M * P)) :
    (1 + P * M)⁻¹ * P = P * (1 + M * P)⁻¹ := by
  have h_mul : (1 + P * M) * ((1 + P * M)⁻¹ * P) = (1 + P * M) * (P * (1 + M * P)⁻¹) := by
    simp_all +decide [ Matrix.isUnit_iff_isUnit_det ];
    simp +decide [ add_mul, mul_assoc ];
    simp +decide [ ← mul_assoc, ← add_mul ];
    rw [ show P + P * M * P = P * ( 1 + M * P ) by rw [ mul_add, mul_one, ← mul_assoc ], Matrix.mul_assoc, Matrix.mul_nonsing_inv _ ( show IsUnit _ from isUnit_iff_ne_zero.mpr hMP ), mul_one ];
  apply_fun fun x => ( 1 + P * M ) ⁻¹ * x at h_mul ; simp_all +decide [ Matrix.isUnit_iff_isUnit_det ]
