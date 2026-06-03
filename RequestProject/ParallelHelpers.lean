/-
# Helper lemmas for the parallel Riccati recursion

Elementary matrix and vector identities needed for the correctness proofs.
-/
import Mathlib

open Matrix

set_option maxHeartbeats 800000

variable {n m : ℕ} [DecidableEq (Fin n)] [DecidableEq (Fin m)]

/-
═══════════════════════════════════════════════════════════════════════════
§ 1. dotProduct / mulVec identities
═══════════════════════════════════════════════════════════════════════════

Transpose identity: x ⬝ᵥ M·u = (Mᵀ·x) ⬝ᵥ u
-/
lemma dotProduct_mulVec_eq_transpose
    (M : Matrix (Fin n) (Fin m) ℝ) (x : Fin n → ℝ) (u : Fin m → ℝ) :
    x ⬝ᵥ M.mulVec u = (Mᵀ.mulVec x) ⬝ᵥ u := by
  simp +decide [ Matrix.mulVec, dotProduct, Finset.mul_sum ] ; ring;
  simpa only [ Finset.sum_mul _ _ _ ] using Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring )

/-
mulVec associativity: M·(N·v) = (M*N)·v
-/
lemma mulVec_mulVec_eq
    (M : Matrix (Fin n) (Fin m) ℝ) (N : Matrix (Fin m) (Fin m) ℝ) (v : Fin m → ℝ) :
    M.mulVec (N.mulVec v) = (M * N).mulVec v := by
  simp +decide [ ← Matrix.mul_assoc ]

/-
═══════════════════════════════════════════════════════════════════════════
§ 2. Completing the square for the control variable
═══════════════════════════════════════════════════════════════════════════

At u = -R⁻¹w, the quadratic ½uᵀRu + wᵀu = -½wᵀR⁻¹w.

Proof: R·u = R·(-R⁻¹w) = -w (using R·R⁻¹ = I from hR).
So u ⬝ᵥ R·u = (-R⁻¹w) ⬝ᵥ (-w) = (R⁻¹w) ⬝ᵥ w.
And w ⬝ᵥ u = -w ⬝ᵥ R⁻¹w.
So ½(R⁻¹w) ⬝ᵥ w - w ⬝ᵥ R⁻¹w = -½ w ⬝ᵥ R⁻¹w.
-/
theorem completing_square_control
    (R : Matrix (Fin m) (Fin m) ℝ) (w : Fin m → ℝ)
    (hR : IsUnit R) :
    let u := -(R⁻¹).mulVec w
    (1/2 : ℝ) * (u ⬝ᵥ R.mulVec u) + w ⬝ᵥ u =
    -(1/2 : ℝ) * (w ⬝ᵥ R⁻¹.mulVec w) := by
  simp +decide [ Matrix.isUnit_iff_isUnit_det ] at hR ⊢;
  simp +decide [ Matrix.mulVec_mulVec, hR, Matrix.mulVec_neg, dotProduct_comm ];
  ring

/-
═══════════════════════════════════════════════════════════════════════════
§ 3. Symmetric bilinear form expansion
═══════════════════════════════════════════════════════════════════════════

For a symmetric matrix N, (a+b) ⬝ᵥ N·(a+b) = a ⬝ᵥ Na + 2(a ⬝ᵥ Nb) + b ⬝ᵥ Nb.

Uses a ⬝ᵥ Nb = b ⬝ᵥ Na (symmetry of N).
-/
theorem symm_quadForm_add2
    (N : Matrix (Fin m) (Fin m) ℝ) (a b : Fin m → ℝ)
    (hN : N.IsSymm) :
    (a + b) ⬝ᵥ N.mulVec (a + b) =
    a ⬝ᵥ N.mulVec a + 2 * (a ⬝ᵥ N.mulVec b) + b ⬝ᵥ N.mulVec b := by
  simp +decide [ Matrix.mulVec_add, add_mul, mul_add, dotProduct_add, two_mul, add_assoc ];
  simp +decide [ Matrix.mulVec, dotProduct ];
  simp +decide only [Finset.mul_sum _ _ _, mul_left_comm];
  rw [ Finset.sum_comm ] ; congr ; ext ; congr ; ext ; ring;
  rw [ ← hN.apply ] ; ring!;

/-
For symmetric N, a ⬝ᵥ N·b = b ⬝ᵥ N·a.
-/
theorem symm_dotProduct_mulVec_comm
    (N : Matrix (Fin m) (Fin m) ℝ) (a b : Fin m → ℝ)
    (hN : N.IsSymm) :
    a ⬝ᵥ N.mulVec b = b ⬝ᵥ N.mulVec a := by
  simp +decide [ Matrix.mulVec, dotProduct ];
  simp +decide only [Finset.mul_sum _ _ _, mul_left_comm, mul_comm];
  exact Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by rw [ ← Matrix.IsSymm.apply hN ] )

/-
For symmetric N, (a+b+c) ⬝ᵥ N·(a+b+c)
    = a ⬝ᵥ Na + b ⬝ᵥ Nb + c ⬝ᵥ Nc + 2(a ⬝ᵥ Nb) + 2(a ⬝ᵥ Nc) + 2(b ⬝ᵥ Nc).
-/
theorem symm_quadForm_add3
    (N : Matrix (Fin m) (Fin m) ℝ) (a b c : Fin m → ℝ)
    (hN : N.IsSymm) :
    (a + b + c) ⬝ᵥ N.mulVec (a + b + c) =
    a ⬝ᵥ N.mulVec a + b ⬝ᵥ N.mulVec b + c ⬝ᵥ N.mulVec c +
    2 * (a ⬝ᵥ N.mulVec b) + 2 * (a ⬝ᵥ N.mulVec c) + 2 * (b ⬝ᵥ N.mulVec c) := by
  convert symm_quadForm_add2 N ( a + b ) c ( hN ) using 1 ; ring;
  rw [ symm_quadForm_add2 N a b hN ] ; ring;
  simp +decide [ Matrix.mulVec_add, dotProduct_add ] ; ring;

/-
═══════════════════════════════════════════════════════════════════════════
§ 4. Key matrix identity for the Schur complement
═══════════════════════════════════════════════════════════════════════════

If G = R + D (with R, G invertible), then R⁻¹ D G⁻¹ = R⁻¹ - G⁻¹.

Proof: R⁻¹(G-R)G⁻¹ = R⁻¹GG⁻¹ - R⁻¹RG⁻¹ = R⁻¹ - G⁻¹.
-/
theorem inv_diff_decomp
    (R G : Matrix (Fin m) (Fin m) ℝ) (D : Matrix (Fin m) (Fin m) ℝ)
    (hR : IsUnit R) (hG : IsUnit G) (hD : G = R + D) :
    R⁻¹ * D * G⁻¹ = R⁻¹ - G⁻¹ := by
  have hD' : D = G - R := by
    rw [ hD, add_sub_cancel_left ];
  simp +decide [ hD', mul_sub, sub_mul ];
  cases hG.nonempty_invertible ; cases hR.nonempty_invertible ; simp +decide [ Matrix.mul_inv_rev ]

/-
Variant: G⁻¹ D R⁻¹ = R⁻¹ - G⁻¹
-/
theorem inv_diff_decomp'
    (R G : Matrix (Fin m) (Fin m) ℝ) (D : Matrix (Fin m) (Fin m) ℝ)
    (hR : IsUnit R) (hG : IsUnit G) (hD : G = R + D) :
    G⁻¹ * D * R⁻¹ = R⁻¹ - G⁻¹ := by
  simp_all +decide [ mul_add, add_mul, mul_assoc, Matrix.isUnit_iff_isUnit_det ];
  convert congr_arg ( fun x => ( R + D ) ⁻¹ * x ) ( show D * R⁻¹ = ( R + D ) * R⁻¹ - 1 by simp +decide [ add_mul, hR, isUnit_iff_ne_zero ] ) using 1 ; simp +decide [ mul_sub, sub_mul, hR, hG, isUnit_iff_ne_zero ]

/-
═══════════════════════════════════════════════════════════════════════════
§ 5. Inverse symmetry
═══════════════════════════════════════════════════════════════════════════

The inverse of a symmetric matrix is symmetric.
-/
theorem IsSymm.inv (M : Matrix (Fin m) (Fin m) ℝ) (hM : M.IsSymm) :
    M⁻¹.IsSymm := by
  rw [ Matrix.IsSymm, Matrix.transpose_nonsing_inv, hM ]