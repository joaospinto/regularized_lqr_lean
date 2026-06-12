/-
# Block-tridiagonal `LDLᵀ` factorization and inertia certification

This file removes the one structural hypothesis that the previous inertia
certification (`RiccatiCertification.riccati_inertia_certification`) had to take
as input: the block-`LDLᵀ` factorization
`M = Lᵀ · diag(pivots) · L` of the reduced primal Hessian.

The mathematical content is the paper's observation
(`\label{riccati-inertia-certification-theorem}`) that

> the sequential Riccati recursion is a block `LDLᵀ` factorization of the
> reduced primal Hessian.

We prove this *as a theorem about block-tridiagonal matrices*, by induction with
Schur complements working from the top-left block to the bottom-right one (which,
under the natural relabeling stage `0 ↦ N`, is exactly the bottom-right-to-top-left
elimination order of the backward recursion).

## Setup

A symmetric block-tridiagonal matrix on stages `s, s+1, …, s+k` is assembled from

* diagonal blocks `dia i : Matrix (β i) (β i) ℝ`, and
* sub-diagonal coupling blocks `off i : Matrix (β (i+1)) (β i) ℝ`

via the recursive index type `Idx β s k = β s ⊕ β (s+1) ⊕ … ⊕ β (s+k)` and the
matrix `assemble dia off s k fd`, where `fd` overrides the head diagonal block
(this is what lets the Schur recursion modify the leading pivot in place).

The Schur pivots are produced by the recursion `AllPivotsPD`:
eliminating the head block `fd` uses it as a pivot and replaces the next
diagonal block by its Schur complement `dia (s+1) − off s · fd⁻¹ · (off s)ᵀ`.

## Main results

* `posDef_fromBlocks_iff` — the `2×2` positive-definite Schur step:
  `[[A, B],[Bᵀ, D]] ≻ 0 ↔ A ≻ 0 ∧ (D − Bᵀ A⁻¹ B) ≻ 0`.
* `assemble_posDef_iff` — the block-tridiagonal matrix is positive definite iff
  every Schur pivot is positive definite (the `LDLᵀ` certification, by induction).
* `riccati_inertia_certification_tridiag` — the inertia-certification theorem with
  the factorization **derived** rather than assumed: if the reduced Hessian
  `P + Cᵀ Δ⁻¹ C` is (a reindexing of) a block-tridiagonal matrix, then
  `K_LQR = [[P, Cᵀ], [C, −Δ]]` has the descent-certifying inertia iff every Schur
  (Riccati) pivot is positive definite.
-/
import Mathlib
import RequestProject.KKTInertia
import RequestProject.RiccatiCertification

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

open Matrix
open scoped Matrix

namespace BlockTridiagLDL

open KKTInertia

/-! ## The `2×2` positive-definite Schur step -/

/-
A block-diagonal matrix is positive definite iff both diagonal blocks are.
-/
theorem posDef_fromBlocks_diag {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (A : Matrix m m ℝ) (D : Matrix n n ℝ) :
    (fromBlocks A 0 0 D).PosDef ↔ A.PosDef ∧ D.PosDef := by
  constructor;
  · rintro ⟨ hA, hD ⟩;
    constructor <;> constructor;
    · ext i j; have := congr_fun ( congr_fun hA ( Sum.inl i ) ) ( Sum.inl j ) ; aesop;
    · intro x hx; specialize hD ( show Finsupp.equivFunOnFinite.symm ( Sum.elim x 0 ) ≠ 0 from by simpa [ Finsupp.ext_iff ] using hx ) ; simp_all +decide [ Finsupp.sum_fintype ] ;
    · ext i j; have := congr_fun ( congr_fun hA ( Sum.inr i ) ) ( Sum.inr j ) ; aesop;
    · intro x hx; specialize hD ( show Finsupp.equivFunOnFinite.symm ( Sum.elim 0 x ) ≠ 0 from by simpa [ Finsupp.ext_iff ] using hx ) ; simp_all +decide [ Finsupp.sum_fintype ] ;
  · rintro ⟨ hA, hD ⟩;
    constructor;
    · simp_all +decide [ Matrix.IsHermitian, Matrix.fromBlocks_transpose ];
      exact ⟨ hA.1, hD.1 ⟩;
    · intro x hx_ne;
      -- Split the sum into two parts: one over `m` and one over `n`.
      have h_split : x.sum (fun i xi => x.sum (fun j xj => star xi * fromBlocks A 0 0 D i j * xj)) = (x.comapDomain (Sum.inl) (by simp)).sum (fun i xi => (x.comapDomain (Sum.inl) (by simp)).sum (fun j xj => star xi * A i j * xj)) + (x.comapDomain (Sum.inr) (by simp)).sum (fun i xi => (x.comapDomain (Sum.inr) (by simp)).sum (fun j xj => star xi * D i j * xj)) := by
        simp +decide [ Finsupp.sum_fintype, Finsupp.comapDomain ];
      by_cases hx_left : Finsupp.comapDomain Sum.inl x (by simp) = 0 <;> by_cases hx_right : Finsupp.comapDomain Sum.inr x (by simp) = 0 <;> simp_all +decide [ Matrix.PosDef ];
      · simp_all +decide [ Finsupp.ext_iff, Finsupp.comapDomain ];
      · exact add_pos ( hA.2 hx_left ) ( hD.2 hx_right )

/-
**`2×2` positive-definite Schur step.** A symmetric `2×2` block matrix is
positive definite iff its top-left block and the corresponding Schur complement
are both positive definite. No symmetry hypothesis is needed: positive
definiteness of the whole forces the relevant blocks to be Hermitian.
-/
theorem posDef_fromBlocks_iff {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (A : Matrix m m ℝ) (B : Matrix m n ℝ)
    (D : Matrix n n ℝ) :
    (fromBlocks A B Bᵀ D).PosDef ↔ A.PosDef ∧ (D - Bᵀ * A⁻¹ * B).PosDef := by
  constructor <;> intro h;
  · have hA : A.PosDef := by
      have := h.2;
      constructor;
      · ext i j; have := h.1; simp_all +decide [ Matrix.IsHermitian ] ;
        replace this := congr_fun ( congr_fun this ( Sum.inl i ) ) ( Sum.inl j ) ; aesop;
      · intro x hx; specialize this ( show ( Finsupp.equivFunOnFinite.symm ( Sum.elim x 0 ) ) ≠ 0 from by simpa [ Finsupp.ext_iff ] using hx ) ; simp_all +decide [ Finsupp.sum_fintype ] ;
    have h_congr : (Matrix.fromBlocks A 0 0 (D - Bᵀ * A⁻¹ * B)).PosDef := by
      have h_congr : ∃ U : Matrix (m ⊕ n) (m ⊕ n) ℝ, IsUnit U ∧ (fromBlocks A B Bᵀ D) = U.transpose * (fromBlocks A 0 0 (D - Bᵀ * A⁻¹ * B)) * U := by
        have h_congr : fromBlocks A B Bᵀ D = fromBlocks 1 0 (Bᵀ * A⁻¹) 1 * fromBlocks A 0 0 (D - Bᵀ * A⁻¹ * B) * fromBlocks 1 (A⁻¹ * B) 0 1 := by
          simp +decide [ Matrix.fromBlocks_multiply, Matrix.mul_assoc ];
          simp +decide [ ← Matrix.mul_assoc, hA.det_pos.ne', isUnit_iff_ne_zero ];
        refine' ⟨ fromBlocks 1 ( A⁻¹ * B ) 0 1, _, _ ⟩;
        · simp +decide [ Matrix.isUnit_iff_isUnit_det ];
        · convert h_congr using 1;
          simp +decide [ Matrix.fromBlocks_transpose, Matrix.transpose_nonsing_inv ];
          rw [ show Aᵀ = A from hA.1 ];
      obtain ⟨ U, hU, h ⟩ := h_congr;
      have := RiccatiCertification.posDef_congr_iff ( fromBlocks A 0 0 ( D - Bᵀ * A⁻¹ * B ) ) hU;
      exact this.mp ( h ▸ by assumption );
    exact ⟨ hA, by simpa using posDef_fromBlocks_diag A ( D - Bᵀ * A⁻¹ * B ) |>.1 h_congr |>.2 ⟩;
  · have h_inv : Invertible A := by
      convert Matrix.invertibleOfDetInvertible A;
      exact invertibleOfNonzero h.1.det_pos.ne';
    have h_congr : (fromBlocks A B Bᵀ D) = (fromBlocks 1 0 (Bᵀ * ⅟A) 1) * (fromBlocks A 0 0 (D - Bᵀ * ⅟A * B)) * (fromBlocks 1 (⅟A * B) 0 1) := by
      convert Matrix.fromBlocks_eq_of_invertible₁₁ A B Bᵀ D using 1;
    have h_congr : (fromBlocks A 0 0 (D - Bᵀ * ⅟A * B)).PosDef := by
      convert posDef_fromBlocks_diag A ( D - Bᵀ * A⁻¹ * B ) |>.2 ⟨ h.1, h.2 ⟩ using 1;
      simp +decide [ Matrix.invOf_eq_nonsing_inv ];
    have h_congr : IsUnit (fromBlocks 1 (⅟A * B) 0 1 : Matrix (m ⊕ n) (m ⊕ n) ℝ) := by
      simp +decide [ Matrix.isUnit_iff_isUnit_det ];
    have h_congr : (fromBlocks 1 (⅟A * B) 0 1 : Matrix (m ⊕ n) (m ⊕ n) ℝ).transpose * (fromBlocks A 0 0 (D - Bᵀ * ⅟A * B)) * (fromBlocks 1 (⅟A * B) 0 1) = fromBlocks A B Bᵀ D := by
      simp_all +decide [ Matrix.fromBlocks_transpose ];
      have := h.1.1; simp_all +decide [ Matrix.IsHermitian, Matrix.transpose_nonsing_inv ] ;
    exact h_congr ▸ RiccatiCertification.posDef_congr_iff _ ‹_› |>.2 ‹_›

/-! ## Recursive index type for block-tridiagonal matrices -/

/-- `Idx β s k` is the disjoint union `β s ⊕ β (s+1) ⊕ … ⊕ β (s+k)` of the
block index types of stages `s, …, s+k`. -/
def Idx (β : ℕ → Type) : ℕ → ℕ → Type
  | s, 0 => β s
  | s, (k+1) => β s ⊕ Idx β (s+1) k

instance idxFin (β : ℕ → Type) [∀ i, Fintype (β i)] : (s k : ℕ) → Fintype (Idx β s k)
  | _, 0 => inferInstanceAs (Fintype (β _))
  | s, (k+1) => letI := idxFin β (s+1) k; inferInstanceAs (Fintype (β s ⊕ Idx β (s+1) k))

instance idxDec (β : ℕ → Type) [∀ i, DecidableEq (β i)] : (s k : ℕ) → DecidableEq (Idx β s k)
  | _, 0 => inferInstanceAs (DecidableEq (β _))
  | s, (k+1) => letI := idxDec β (s+1) k; inferInstanceAs (DecidableEq (β s ⊕ Idx β (s+1) k))

variable {β : ℕ → Type} [∀ i, Fintype (β i)] [∀ i, DecidableEq (β i)]

/-- Embed a head-block matrix `X : Matrix (β s) (β (s+1))` as the coupling block
`Matrix (β s) (Idx β (s+1) k)` between stage `s` and the rest of the chain (it is
`X` on the `β (s+1)` columns and `0` on all later columns). -/
def cplOf (β : ℕ → Type) [∀ i, Fintype (β i)] [∀ i, DecidableEq (β i)] :
    (s k : ℕ) → Matrix (β s) (β (s+1)) ℝ → Matrix (β s) (Idx β (s+1) k) ℝ
  | _, 0, X => X
  | _, _+1, X => Matrix.of (fun i j => Sum.elim (fun j' => X i j') (fun _ => 0) j)

/-- Embed a head-block matrix `Y : Matrix (β s) (β s)` into the full chain index,
placing `Y` in the top-left block and `0` everywhere else. -/
def embedHead (β : ℕ → Type) [∀ i, Fintype (β i)] [∀ i, DecidableEq (β i)] :
    (s k : ℕ) → Matrix (β s) (β s) ℝ → Matrix (Idx β s k) (Idx β s k) ℝ
  | _, 0, Y => Y
  | _, _+1, Y => fromBlocks Y 0 0 0

/-- The symmetric block-tridiagonal matrix on stages `s, …, s+k` with diagonal
blocks `dia` (head block overridden by `fd`) and sub-diagonal coupling `off`. -/
def assemble (dia : ∀ i, Matrix (β i) (β i) ℝ) (off : ∀ i, Matrix (β (i+1)) (β i) ℝ) :
    (s k : ℕ) → Matrix (β s) (β s) ℝ → Matrix (Idx β s k) (Idx β s k) ℝ
  | _, 0, fd => fd
  | s, k+1, fd =>
      fromBlocks fd (cplOf β s k (off s)ᵀ) ((cplOf β s k (off s)ᵀ)ᵀ)
        (assemble dia off (s+1) k (dia (s+1)))

/-- The Schur-pivot recursion: positive definiteness of every pivot produced by
eliminating the head block `fd` and updating the next diagonal block by its Schur
complement. -/
def AllPivotsPD (dia : ∀ i, Matrix (β i) (β i) ℝ) (off : ∀ i, Matrix (β (i+1)) (β i) ℝ) :
    (s k : ℕ) → Matrix (β s) (β s) ℝ → Prop
  | _, 0, fd => fd.PosDef
  | s, k+1, fd =>
      fd.PosDef ∧ AllPivotsPD dia off (s+1) k (dia (s+1) - off s * fd⁻¹ * (off s)ᵀ)

/-
The coupling block, conjugated by any middle matrix `mm`, lands exactly in the
top-left block of the chain index: `cplOfᵀ · mm · cplOf = embedHead (Xᵀ · mm · X)`.
-/
theorem cplOf_conj (s k : ℕ) (X : Matrix (β s) (β (s+1)) ℝ) (mm : Matrix (β s) (β s) ℝ) :
    (cplOf β s k X)ᵀ * mm * (cplOf β s k X)
      = embedHead β (s+1) k (Xᵀ * mm * X) := by
  induction' k with k ih generalizing s;
  · rfl;
  · ext i j;
    cases i <;> cases j <;> simp +decide [ Matrix.mul_apply, cplOf, embedHead ]

/-
Subtracting `Y` from the head block of the assembled matrix subtracts the
top-left embedding of `Y` from the whole matrix.
-/
theorem assemble_head_sub (dia : ∀ i, Matrix (β i) (β i) ℝ)
    (off : ∀ i, Matrix (β (i+1)) (β i) ℝ) (s k : ℕ)
    (g Y : Matrix (β s) (β s) ℝ) :
    assemble dia off s k (g - Y) = assemble dia off s k g - embedHead β s k Y := by
  by_contra h_contra;
  induction' k with k ih generalizing s g Y;
  · exact h_contra ( by unfold assemble embedHead; rfl );
  · simp_all +decide [ fromBlocks, embedHead, assemble ];
    exact h_contra <| by ext i j; cases i <;> cases j <;> simp +decide [ Matrix.sub_apply ] ;

/-
**Block-tridiagonal `LDLᵀ` certification.** A symmetric block-tridiagonal
matrix is positive definite iff every Schur (Riccati) pivot is positive definite.
This is the algebraic content of "the sequential Riccati recursion is a block
`LDLᵀ` factorization of the reduced primal Hessian", proved by induction with
Schur complements.
-/
theorem assemble_posDef_iff (dia : ∀ i, Matrix (β i) (β i) ℝ)
    (off : ∀ i, Matrix (β (i+1)) (β i) ℝ) (s k : ℕ) (fd : Matrix (β s) (β s) ℝ) :
    (assemble dia off s k fd).PosDef ↔ AllPivotsPD dia off s k fd := by
  induction' k with k ih generalizing s fd;
  · rfl;
  · convert posDef_fromBlocks_iff fd ( cplOf β s k ( off s ) ᵀ ) ( assemble dia off ( s + 1 ) k ( dia ( s + 1 ) ) ) using 1;
    rw [ cplOf_conj ];
    rw [ ← assemble_head_sub ] ; aesop;

/-! ## Inertia certification with the factorization derived -/

/-- **Riccati inertia certification, factorization derived**
(`\label{riccati-inertia-certification-theorem}`).

Let `K_LQR = [[P, Cᵀ], [C, −Δ]]` with `Δ ≻ 0`. Suppose the reduced primal Hessian
`P + Cᵀ Δ⁻¹ C` is, up to reindexing by `e`, the block-tridiagonal matrix assembled
from the stage data `dia`, `off`. Then `K_LQR` has the descent-certifying inertia
`(card ι, card κ, 0)` **iff** every Schur (Riccati) pivot is positive definite.

Unlike `RiccatiCertification.riccati_inertia_certification`, the `LDLᵀ`
factorization is no longer assumed: it is the proven theorem `assemble_posDef_iff`.
-/
theorem riccati_inertia_certification_tridiag
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (P : Matrix ι ι ℝ) (C : Matrix κ ι ℝ) (Δ : Matrix κ κ ℝ)
    (hP : P.IsHermitian) (hΔ : Δ.PosDef)
    (dia : ∀ i, Matrix (β i) (β i) ℝ) (off : ∀ i, Matrix (β (i+1)) (β i) ℝ)
    (k : ℕ) (e : ι ≃ Idx β 0 k)
    (heq : P + Cᵀ * Δ⁻¹ * C = (assemble dia off 0 k (dia 0)).submatrix e e) :
    HasInertia (fromBlocks P Cᵀ C (-Δ)) (Fintype.card ι) (Fintype.card κ) 0
      ↔ AllPivotsPD dia off 0 k (dia 0) := by
  rw [KKTInertia.kkt_inertia_iff P C Δ hP hΔ, heq,
    RiccatiCertification.posDef_submatrix_equiv e (assemble dia off 0 k (dia 0)),
    assemble_posDef_iff]

end BlockTridiagLDL