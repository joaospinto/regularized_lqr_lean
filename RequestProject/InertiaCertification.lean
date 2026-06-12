/-
# Inertia certification of the dual-regularized Newton-KKT system

This file fills in several of the inertia results from
"Dual-Regularized Riccati Recursions for Interior-Point Optimal Control"
(Sousa-Pinto & Orban) that were previously left unformalized.  Results are
referenced by their LaTeX `\label{...}` names in the paper source (`main.tex`).

## Reusable inertia infrastructure

* `hasInertia_neg`: negating a matrix swaps its positive and negative inertia
  indices.
* `sylvester_inertia_pos`: the *positive-pivot* variant of Sylvester's law of
  inertia.  For symmetric `H`, arbitrary `A`, and positive-definite `D`,
  eliminating against the positive pivot `D` adds exactly `card κ` *positive*
  directions:
  `In([[H, Aᵀ], [A, D]]) = In(D) + In(H - Aᵀ D⁻¹ A) = (card κ, 0, 0) + In(H - Aᵀ D⁻¹ A)`.
  This complements the negative-pivot `sylvester_inertia` in
  `DescentDirection.lean`.

## Main result: `\label{4x4-3x3-inertia-lemma}`

`k4_k3_inertia`: `In(K₄) = In(K₃) + (n_g, 0, 0)`.  Following the paper, we permute
the variables of `K₄` from `(x, s, y, z)` to `(x, y, z, s)`, obtaining the saddle
matrix `[[M₃, Bᵀ], [B, W⁻¹]]` whose bottom-right pivot `W⁻¹` is positive definite,
where `M₃ = [[P, Cᵀ, Gᵀ], [C, -Δ_C⁻¹], [G, 0, -Δ_G⁻¹]]` is the `(x, y, z)` block
and `B = [0, 0, I]` couples the slack `s` to the inequality multiplier `z`.
Eliminating the slack against `W⁻¹` (the positive-pivot Sylvester variant) yields
the Schur complement `K₃` and contributes `(n_g, 0, 0)` to the inertia.
-/
import Mathlib
import RequestProject.KKTInertia
import RequestProject.DescentDirection
import RequestProject.InertiaChain

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

open Matrix
open scoped Matrix

namespace InertiaCertification

open KKTInertia

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- Negating a symmetric matrix swaps its positive and negative inertia indices:
`M` has inertia `(p, q, z)` iff `-M` has inertia `(q, p, z)`. -/
theorem hasInertia_neg (M : Matrix ι ι ℝ) (p q z : ℕ) :
    HasInertia (-M) q p z ↔ HasInertia M p q z := by
  unfold HasInertia negIndex
  rw [neg_neg]
  constructor
  · rintro ⟨h1, h2, h3⟩; exact ⟨h2, h1, by omega⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨h2, h1, by omega⟩

/-
**Positive-pivot Sylvester inertia lemma.**

For symmetric `H`, arbitrary `A`, and positive-definite `D`, the saddle matrix
`[[H, Aᵀ], [A, D]]` (with a *positive* bottom-right pivot) has inertia
`In(D) + In(H - Aᵀ D⁻¹ A)`.  Since `D ≻ 0`, `In(D) = (card κ, 0, 0)`, so if the
Schur complement `H - Aᵀ D⁻¹ A` has inertia `(p, q, z)`, then the saddle matrix
has inertia `(p + card κ, q, z)`.

This is the positive-pivot counterpart of `DescentDirection.sylvester_inertia`.
-/
theorem sylvester_inertia_pos [DecidableEq ι] [DecidableEq κ]
    (H : Matrix ι ι ℝ) (A : Matrix κ ι ℝ) (D : Matrix κ κ ℝ) (hD : D.PosDef)
    {p q z : ℕ}
    (hSchur : HasInertia (H - Aᵀ * D⁻¹ * A) p q z) :
    HasInertia (fromBlocks H Aᵀ A D) (p + Fintype.card κ) q z := by
  obtain ⟨h₁, h₂, h₃⟩ := hSchur;
  convert hasInertia_neg _ _ _ _ |>.1 _ using 1;
  convert sylvester_inertia ( -H ) ( -A ) D hD _ using 1;
  · ext i j ; aesop;
  · convert hasInertia_neg _ _ _ _ |>.2 ⟨ h₁, h₂, h₃ ⟩ using 1;
    ext i j; simp +decide [ Matrix.mul_apply, Matrix.transpose_apply ] ; ring;

/-! ## The `4×4 → 3×3` inertia lemma (`\label{4x4-3x3-inertia-lemma}`) -/

variable {nx nc ns : ℕ}
  [DecidableEq (Fin nx)] [DecidableEq (Fin nc)] [DecidableEq (Fin ns)]

/-- The slack-coupling block `B = [0 | 0 | I]`: it maps the slack `s` (`Fin ns`)
to the inequality-multiplier `z` block, with zeros on the `(x, y)` block. -/
def colI (nx nc ns : ℕ) [DecidableEq (Fin ns)] :
    Matrix (Fin ns) ((Fin nx ⊕ Fin nc) ⊕ Fin ns) ℝ :=
  Matrix.of fun i j => Sum.elim (fun _ => (0 : ℝ)) (fun jz => (1 : Matrix (Fin ns) (Fin ns) ℝ) i jz) j

/-- The `(x, y, z)` block `M₃ = [[P, Cᵀ, Gᵀ], [C, -Δ_C⁻¹, 0], [G, 0, -Δ_G⁻¹]]`
of the permuted `K₄`. -/
def M3 (P : Matrix (Fin nx) (Fin nx) ℝ) (C : Matrix (Fin nc) (Fin nx) ℝ)
    (DeltaCinv : Matrix (Fin nc) (Fin nc) ℝ) (G : Matrix (Fin ns) (Fin nx) ℝ)
    (DeltaGinv : Matrix (Fin ns) (Fin ns) ℝ) :
    Matrix ((Fin nx ⊕ Fin nc) ⊕ Fin ns) ((Fin nx ⊕ Fin nc) ⊕ Fin ns) ℝ :=
  fromBlocks (fromBlocks P Cᵀ C (-DeltaCinv)) (InertiaChain.rowG0 G)ᵀ
    (InertiaChain.rowG0 G) (-DeltaGinv)

/-- The reduced `3×3` system `K₃ = [[P, Cᵀ, Gᵀ], [C, -Δ_C⁻¹, 0], [G, 0, -(W+Δ_G⁻¹)]]`
(`\label{ipm-3x3-newton-kkt}`), with `W = (W⁻¹)⁻¹`. -/
noncomputable def K3mat (P : Matrix (Fin nx) (Fin nx) ℝ) (C : Matrix (Fin nc) (Fin nx) ℝ)
    (DeltaCinv : Matrix (Fin nc) (Fin nc) ℝ) (G : Matrix (Fin ns) (Fin nx) ℝ)
    (DeltaGinv : Matrix (Fin ns) (Fin ns) ℝ) (Winv : Matrix (Fin ns) (Fin ns) ℝ) :
    Matrix ((Fin nx ⊕ Fin nc) ⊕ Fin ns) ((Fin nx ⊕ Fin nc) ⊕ Fin ns) ℝ :=
  fromBlocks (fromBlocks P Cᵀ C (-DeltaCinv)) (InertiaChain.rowG0 G)ᵀ
    (InertiaChain.rowG0 G) (-(DeltaGinv + Winv⁻¹))

/-
Eliminating the slack against the positive pivot `W⁻¹` turns the permuted
`(x, y, z)` block `M₃` into the `3×3` Schur complement `K₃`:
`M₃ - Bᵀ (W⁻¹)⁻¹ B = K₃`.
-/
theorem schur_eq_k3
    (P : Matrix (Fin nx) (Fin nx) ℝ) (C : Matrix (Fin nc) (Fin nx) ℝ)
    (DeltaCinv : Matrix (Fin nc) (Fin nc) ℝ) (G : Matrix (Fin ns) (Fin nx) ℝ)
    (DeltaGinv : Matrix (Fin ns) (Fin ns) ℝ) (Winv : Matrix (Fin ns) (Fin ns) ℝ) :
    M3 P C DeltaCinv G DeltaGinv - (colI nx nc ns)ᵀ * Winv⁻¹ * colI nx nc ns
      = K3mat P C DeltaCinv G DeltaGinv Winv := by
  ext i j; norm_num [ Matrix.mul_apply, colI ] ;
  rcases i with ( ( i | i ) | i ) <;> rcases j with ( ( j | j ) | j ) <;> norm_num [ Matrix.one_apply, Matrix.sum_apply, K3mat, M3 ];
  ring

/-- **`4×4 → 3×3` inertia lemma** (`\label{4x4-3x3-inertia-lemma}`).

Permuting `K₄` from `(x, s, y, z)` to `(x, y, z, s)` gives the saddle matrix
`[[M₃, Bᵀ], [B, W⁻¹]]`.  Eliminating the slack against the positive-definite pivot
`W⁻¹` yields the Schur complement `K₃` and adds exactly `n_g` positive directions:
`In(K₄) = In(K₃) + (n_g, 0, 0)`. -/
theorem k4_k3_inertia
    (P : Matrix (Fin nx) (Fin nx) ℝ) (C : Matrix (Fin nc) (Fin nx) ℝ)
    (DeltaCinv : Matrix (Fin nc) (Fin nc) ℝ) (G : Matrix (Fin ns) (Fin nx) ℝ)
    (DeltaGinv : Matrix (Fin ns) (Fin ns) ℝ) (Winv : Matrix (Fin ns) (Fin ns) ℝ)
    (hW : Winv.PosDef) {p q z : ℕ}
    (hk3 : HasInertia (K3mat P C DeltaCinv G DeltaGinv Winv) p q z) :
    HasInertia
      (fromBlocks (M3 P C DeltaCinv G DeltaGinv) (colI nx nc ns)ᵀ (colI nx nc ns) Winv)
        (p + ns) q z := by
  have h := sylvester_inertia_pos (M3 P C DeltaCinv G DeltaGinv) (colI nx nc ns) Winv hW
    (p := p) (q := q) (z := z) (by rw [schur_eq_k3]; exact hk3)
  simpa using h

/-! ## The `K₄ ↔ LQR` inertia equivalence -/

/-
Positive-pivot Sylvester, positive-index form: eliminating against a
positive-definite pivot `D` adds exactly `card κ` positive directions.
-/
theorem posIndex_sylvester_pos [DecidableEq ι] [DecidableEq κ]
    (H : Matrix ι ι ℝ) (A : Matrix κ ι ℝ) (D : Matrix κ κ ℝ) (hD : D.PosDef) :
    posIndex (fromBlocks H Aᵀ A D) = posIndex (H - Aᵀ * D⁻¹ * A) + Fintype.card κ := by
  convert KKTInertia.kkt_negIndex ( -H ) ( -A ) D hD using 1;
  · simp +decide [ negIndex, posIndex ];
    simp +decide [ Matrix.fromBlocks_neg ];
  · simp +decide [ negIndex, Matrix.transpose_neg, Matrix.neg_mul, Matrix.mul_neg, sub_eq_add_neg ];
    rw [ add_comm ]

/-
Positive-pivot Sylvester, negative-index form: eliminating against a
positive-definite pivot preserves the negative index.
-/
theorem negIndex_sylvester_pos [DecidableEq ι] [DecidableEq κ]
    (H : Matrix ι ι ℝ) (A : Matrix κ ι ℝ) (D : Matrix κ κ ℝ) (hD : D.PosDef) :
    negIndex (fromBlocks H Aᵀ A D) = negIndex (H - Aᵀ * D⁻¹ * A) := by
  unfold negIndex;
  convert KKTInertia.kkt_posIndex ( -H ) ( -A ) D hD using 1;
  · simp +decide [ Matrix.fromBlocks_neg, Matrix.transpose_neg ];
  · exact congr_arg _ ( by ext i j; simp +decide ; ring )

/-- The `2×2` reduced system `K_{xy} = [[P + Gᵀ(W+Δ_G⁻¹)⁻¹G, Cᵀ], [C, -Δ_C⁻¹]]`
(`\label{3x3-2x2-inertia-lemma}`).  With `W = (W⁻¹)⁻¹`, this is precisely the
first-order optimality matrix of the *dual-regularized LQR* problem obtained from
the interior-point Newton-KKT system by block-eliminating the slacks `s` and the
inequality multipliers `z`: its cost Hessian is `P + Gᵀ(W+Δ_G⁻¹)⁻¹G`, its
constraint Jacobian is `C`, and its dual regularization is `Δ_C⁻¹`. -/
noncomputable def KxyMat (P : Matrix (Fin nx) (Fin nx) ℝ) (C : Matrix (Fin nc) (Fin nx) ℝ)
    (DeltaCinv : Matrix (Fin nc) (Fin nc) ℝ) (G : Matrix (Fin ns) (Fin nx) ℝ)
    (DeltaGinv : Matrix (Fin ns) (Fin ns) ℝ) (Winv : Matrix (Fin ns) (Fin ns) ℝ) :
    Matrix (Fin nx ⊕ Fin nc) (Fin nx ⊕ Fin nc) ℝ :=
  fromBlocks (P + Gᵀ * (DeltaGinv + Winv⁻¹)⁻¹ * G) Cᵀ C (-DeltaCinv)

/-
The positive index of the (permuted) `K₄` exceeds that of the reduced LQR
matrix `K_{xy}` by exactly `n_g`.
-/
theorem posIndex_k4_kxy
    (P : Matrix (Fin nx) (Fin nx) ℝ) (C : Matrix (Fin nc) (Fin nx) ℝ)
    (DeltaCinv : Matrix (Fin nc) (Fin nc) ℝ) (G : Matrix (Fin ns) (Fin nx) ℝ)
    (DeltaGinv : Matrix (Fin ns) (Fin ns) ℝ) (Winv : Matrix (Fin ns) (Fin ns) ℝ)
    (hW : Winv.PosDef) (hDG : DeltaGinv.PosDef) :
    posIndex (fromBlocks (M3 P C DeltaCinv G DeltaGinv) (colI nx nc ns)ᵀ (colI nx nc ns) Winv)
      = posIndex (KxyMat P C DeltaCinv G DeltaGinv Winv) + ns := by
  have := @KKTInertia.kkt_posIndex;
  rw [ posIndex_sylvester_pos ];
  rw [ schur_eq_k3 ];
  convert congr_arg ( · + ns ) ( this ( fromBlocks P Cᵀ C ( -DeltaCinv ) ) ( InertiaChain.rowG0 G ) ( DeltaGinv + Winv⁻¹ ) _ ) using 1;
  · norm_num [ K3mat ];
  · rw [ InertiaChain.schur_eq_kxy ];
    rfl;
  · exact hDG.add ( hW.inv );
  · exact hW

/-
The negative index of the (permuted) `K₄` exceeds that of the reduced LQR
matrix `K_{xy}` by exactly `n_g`.
-/
theorem negIndex_k4_kxy
    (P : Matrix (Fin nx) (Fin nx) ℝ) (C : Matrix (Fin nc) (Fin nx) ℝ)
    (DeltaCinv : Matrix (Fin nc) (Fin nc) ℝ) (G : Matrix (Fin ns) (Fin nx) ℝ)
    (DeltaGinv : Matrix (Fin ns) (Fin ns) ℝ) (Winv : Matrix (Fin ns) (Fin ns) ℝ)
    (hW : Winv.PosDef) (hDG : DeltaGinv.PosDef) :
    negIndex (fromBlocks (M3 P C DeltaCinv G DeltaGinv) (colI nx nc ns)ᵀ (colI nx nc ns) Winv)
      = negIndex (KxyMat P C DeltaCinv G DeltaGinv Winv) + ns := by
  convert negIndex_sylvester_pos ( M3 P C DeltaCinv G DeltaGinv ) ( colI nx nc ns ) Winv hW using 1;
  rw [ schur_eq_k3 ];
  convert KKTInertia.kkt_negIndex ( fromBlocks P Cᵀ C ( -DeltaCinv ) ) ( InertiaChain.rowG0 G ) ( DeltaGinv + Winv⁻¹ ) _ |> Eq.symm using 1;
  · rw [ KxyMat, InertiaChain.schur_eq_kxy ];
    norm_num;
  · convert hDG.add ( hW.inv ) using 1

/-- **`K₄ ↔ LQR` inertia equivalence.**

The (permuted) interior-point Newton-KKT matrix `K₄` has the descent-certifying
inertia `(n_x + n_g, n_c + n_g, 0)` **iff** the reduced dual-regularized LQR
first-order optimality matrix `K_{xy}` has inertia `(n_x, n_c, 0)`.  This is the
theorem in `main.tex` (§ before `riccati-rational-identity-theorem`) connecting
the inertia of `K₄` to that of the resulting LQR system; here `n_x = nx`,
`n_c = nc`, `n_g = ns`. -/
theorem k4_kxy_inertia_iff
    (P : Matrix (Fin nx) (Fin nx) ℝ) (C : Matrix (Fin nc) (Fin nx) ℝ)
    (DeltaCinv : Matrix (Fin nc) (Fin nc) ℝ) (G : Matrix (Fin ns) (Fin nx) ℝ)
    (DeltaGinv : Matrix (Fin ns) (Fin ns) ℝ) (Winv : Matrix (Fin ns) (Fin ns) ℝ)
    (hW : Winv.PosDef) (hDG : DeltaGinv.PosDef) :
    HasInertia (fromBlocks (M3 P C DeltaCinv G DeltaGinv) (colI nx nc ns)ᵀ (colI nx nc ns) Winv)
        (nx + ns) (nc + ns) 0
      ↔ HasInertia (KxyMat P C DeltaCinv G DeltaGinv Winv) nx nc 0 := by
  have hp := posIndex_k4_kxy P C DeltaCinv G DeltaGinv Winv hW hDG
  have hn := negIndex_k4_kxy P C DeltaCinv G DeltaGinv Winv hW hDG
  unfold HasInertia
  rw [hp, hn]
  simp only [Fintype.card_sum, Fintype.card_fin]
  constructor
  · rintro ⟨h1, h2, _⟩
    exact ⟨by omega, by omega, by omega⟩
  · rintro ⟨h1, h2, _⟩
    exact ⟨by omega, by omega, by omega⟩

/-- **`K₄ ↔ LQR` inertia equivalence, with explicit stage/state/control counts.**

For a dual-regularized LQR with `N` stages, `n`-dimensional states and
`m`-dimensional controls, the reduced LQR matrix has dimension
`N(n+m)+n` (primal) and `(N+1)n` (dual).  The interior-point `K₄` then has the
descent-certifying inertia `(N(n+m)+n + n_g, (N+1)n + n_g, 0)` iff the LQR
matrix `K_{xy}` has inertia `(N(n+m)+n, (N+1)n, 0)`. -/
theorem k4_kxy_inertia_iff_lqr {N n m ns : ℕ}
    [DecidableEq (Fin (N * (n + m) + n))] [DecidableEq (Fin ((N + 1) * n))]
    [DecidableEq (Fin ns)]
    (P : Matrix (Fin (N * (n + m) + n)) (Fin (N * (n + m) + n)) ℝ)
    (C : Matrix (Fin ((N + 1) * n)) (Fin (N * (n + m) + n)) ℝ)
    (DeltaCinv : Matrix (Fin ((N + 1) * n)) (Fin ((N + 1) * n)) ℝ)
    (G : Matrix (Fin ns) (Fin (N * (n + m) + n)) ℝ)
    (DeltaGinv : Matrix (Fin ns) (Fin ns) ℝ) (Winv : Matrix (Fin ns) (Fin ns) ℝ)
    (hW : Winv.PosDef) (hDG : DeltaGinv.PosDef) :
    HasInertia (fromBlocks (M3 P C DeltaCinv G DeltaGinv)
        (colI (N * (n + m) + n) ((N + 1) * n) ns)ᵀ
        (colI (N * (n + m) + n) ((N + 1) * n) ns) Winv)
        (N * (n + m) + n + ns) ((N + 1) * n + ns) 0
      ↔ HasInertia (KxyMat P C DeltaCinv G DeltaGinv Winv) (N * (n + m) + n) ((N + 1) * n) 0 :=
  k4_kxy_inertia_iff P C DeltaCinv G DeltaGinv Winv hW hDG

end InertiaCertification