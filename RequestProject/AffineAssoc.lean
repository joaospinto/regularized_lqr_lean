/-
# Associativity of Affine Function Composition

From Section "Composing Affine Functions with Associative Scans" of the paper.

Given affine functions F_i(x) = M_i x + m_i, we define the composition operator
  f((a, B), (c, D)) = (D * a + c, D * B)
and prove it is associative: f(f(p, q), r) = f(p, f(q, r)).

This is used to parallelize the forward pass of the Riccati recursion
via associative scans.
-/
import Mathlib

open Matrix

variable {n : ℕ} {F : Type*} [Field F] [DecidableEq (Fin n)]

/-- The affine composition operator: composing (x ↦ Bx + a) with (x ↦ Dx + c)
    gives (x ↦ (DB)x + (Da + c)). We represent affine maps as (offset, matrix) pairs. -/
noncomputable def affineCompose
    (p : (Fin n → F) × Matrix (Fin n) (Fin n) F)
    (q : (Fin n → F) × Matrix (Fin n) (Fin n) F) :
    (Fin n → F) × Matrix (Fin n) (Fin n) F :=
  (q.2.mulVec p.1 + q.1, q.2 * p.2)

/-
The affine composition operator is associative.
    This is the key property enabling parallelization via associative scans.
-/
omit [DecidableEq (Fin n)] in
theorem affineCompose_assoc
    (p q r : (Fin n → F) × Matrix (Fin n) (Fin n) F) :
    affineCompose (affineCompose p q) r = affineCompose p (affineCompose q r) := by
  unfold affineCompose;
  simp +decide [ Matrix.mulVec_add, Matrix.mulVec_mulVec, add_assoc ];
  rw [ Matrix.mul_assoc ]
