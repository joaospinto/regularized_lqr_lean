/-
# Intermediate inertia decompositions of the Newton-KKT matrix

This file formalizes the intermediate block-elimination inertia lemma from
"Dual-Regularized Riccati Recursions for Interior-Point Optimal Control"
(Sousa-Pinto & Orban), referenced by its LaTeX label:

* `k3_kxy_inertia` (`\label{3x3-2x2-inertia-lemma}`):
  eliminating the inequality multiplier `Δz` from the `3×3` system `K₃`
  (`\label{ipm-3x3-newton-kkt}`) gives the `2×2` Schur complement `K_{xy}`,
  with `In(K₃) = In(K_{xy}) + (0, n_g, 0)`.

This is an instance of Sylvester's law of inertia (`sylvester_inertia` in
`DescentDirection.lean`), eliminating against the positive-definite pivot
`W+Δ_G⁻¹`. It is one of the stepping stones the paper uses to reach the primal
Schur complement `K_{xs}` and the descent theorem
`\label{inertia-al-descent-theorem}` (formalized directly in
`DescentDirection.lean` via `sylvester_inertia` + `primal_schur_posDef`). The
companion `\label{4x4-3x3-inertia-lemma}` (eliminating the slack `Δs` against the
positive-definite pivot `W⁻¹`) follows by the same Sylvester principle.
-/
import Mathlib
import RequestProject.KKTInertia
import RequestProject.DescentDirection

set_option linter.unusedSectionVars false

open Matrix KKTInertia

namespace InertiaChain

variable {nx nc ns : ℕ}
  [DecidableEq (Fin nx)] [DecidableEq (Fin nc)] [DecidableEq (Fin ns)]

/-- The row block `A = [G | 0]` coupling the inequality multiplier `z` to the
primal/equality variables `(x, y)`: it acts as `G` on the `x` block and `0` on
the `y` block. -/
def rowG0 (G : Matrix (Fin ns) (Fin nx) ℝ) :
    Matrix (Fin ns) (Fin nx ⊕ Fin nc) ℝ :=
  Matrix.of fun i j => Sum.elim (fun jx => G i jx) (fun _ => 0) j

/-
The primal/equality Schur complement obtained by eliminating `Δz` from `K₃`:
`H + Aᵀ D⁻¹ A` with `H = [[P, Cᵀ], [C, -Δ_C⁻¹]]`, `A = [G | 0]`, `D = W+Δ_G⁻¹`
equals `K_{xy} = [[P + Gᵀ (W+Δ_G⁻¹)⁻¹ G, Cᵀ], [C, -Δ_C⁻¹]]`.
-/
theorem schur_eq_kxy
    (P : Matrix (Fin nx) (Fin nx) ℝ)
    (C : Matrix (Fin nc) (Fin nx) ℝ)
    (DeltaCinv : Matrix (Fin nc) (Fin nc) ℝ)
    (G : Matrix (Fin ns) (Fin nx) ℝ)
    (D : Matrix (Fin ns) (Fin ns) ℝ) :
    (fromBlocks P Cᵀ C (-DeltaCinv)) + (rowG0 G)ᵀ * D⁻¹ * (rowG0 G)
      = fromBlocks (P + Gᵀ * D⁻¹ * G) Cᵀ C (-DeltaCinv) := by
  ext i j;
  rcases i with ( i | i ) <;> rcases j with ( j | j ) <;> norm_num [ Matrix.mul_apply, rowG0 ]

/-
**3×3 → 2×2 inertia lemma** (`\label{3x3-2x2-inertia-lemma}`).

Eliminating the inequality multiplier `Δz` against the positive-definite pivot
`W + Δ_G⁻¹` turns the `3×3` system `K₃` into the `2×2` Schur complement `K_{xy}`,
adding exactly `n_g` negative directions.
-/
theorem k3_kxy_inertia
    (P : Matrix (Fin nx) (Fin nx) ℝ)
    (C : Matrix (Fin nc) (Fin nx) ℝ)
    (DeltaCinv : Matrix (Fin nc) (Fin nc) ℝ)
    (G : Matrix (Fin ns) (Fin nx) ℝ)
    (D : Matrix (Fin ns) (Fin ns) ℝ) (hD : D.PosDef)
    {p q z : ℕ}
    (hxy : HasInertia (fromBlocks (P + Gᵀ * D⁻¹ * G) Cᵀ C (-DeltaCinv)) p q z) :
    HasInertia
      (fromBlocks (fromBlocks P Cᵀ C (-DeltaCinv)) (rowG0 G)ᵀ
        (rowG0 G) (-D)) p (q + ns) z := by
  have h := sylvester_inertia (fromBlocks P Cᵀ C (-DeltaCinv)) (rowG0 G) D hD
    (by rw [schur_eq_kxy]; exact hxy)
  simpa using h

end InertiaChain
