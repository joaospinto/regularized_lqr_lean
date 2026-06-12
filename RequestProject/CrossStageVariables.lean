/-
# Cross-Stage Variables

This file formalizes the linear-algebra content of the *Cross-Stage Variables*
section of "Dual-Regularized Riccati Recursions for Interior-Point Optimal
Control" (Sousa-Pinto & Orban).

In some applications it is useful to introduce a small number of variables
`θ ∈ ℝᵖ` that are shared by every stage (e.g. a global clearance margin in the
quadpendulum benchmark). Keeping `θ` as a global variable rather than folding it
into the state gives the Newton system the *arrowhead* block form

```
  [ K    J_θ ] [ Δw ]      [ r_w ]
  [ J_θᵀ H   ] [ Δθ ]  = - [ r_θ ],
```

where `K` is the dual-regularized LQR (Riccati) matrix. The system is solved by
forming the dense Schur complement in the cross-stage variables,

```
  S_θ = H - J_θᵀ K⁻¹ J_θ,
```

after which

```
  Δθ = -S_θ⁻¹ (r_θ - J_θᵀ K⁻¹ r_w),
  Δw = -K⁻¹ (r_w + J_θ Δθ).
```

The only `K⁻¹` products needed are reused from the Riccati factorization (one
solve against `r_w` and `p` solves against the columns of `J_θ`), keeping the
large block `K` an LQR-structured solve while isolating the nonlocal coupling
in the small `p × p` dense Schur complement.

The theorem `crossStage_schur_solve` below verifies that the stated
`(Δw, Δθ)` indeed solves the arrowhead system, for an arbitrary invertible `K`
and invertible Schur complement `S_θ` over any field. This is the algebraic
guarantee underlying the cross-stage solve; nothing about the internal Riccati
structure of `K` is needed for correctness, only that `K` (and `S_θ`) be
invertible.
-/
import Mathlib

namespace CrossStageVariables

open Matrix

variable {n p : Type*} [Fintype n] [DecidableEq n] [Fintype p] [DecidableEq p]
variable {𝕜 : Type*} [Field 𝕜]

/-- The cross-stage Schur complement `S_θ = H - J_θᵀ K⁻¹ J_θ`. -/
noncomputable def schurθ (K : Matrix n n 𝕜) (J : Matrix n p 𝕜) (H : Matrix p p 𝕜) :
    Matrix p p 𝕜 :=
  H - Jᵀ * K⁻¹ * J

/-- The cross-stage variable step
`Δθ = -S_θ⁻¹ (r_θ - J_θᵀ K⁻¹ r_w)`. -/
noncomputable def deltaθ (K : Matrix n n 𝕜) (J : Matrix n p 𝕜) (H : Matrix p p 𝕜)
    (rw : n → 𝕜) (rθ : p → 𝕜) : p → 𝕜 :=
  -((schurθ K J H)⁻¹ *ᵥ (rθ - Jᵀ *ᵥ (K⁻¹ *ᵥ rw)))

/-- The stagewise step `Δw = -K⁻¹ (r_w + J_θ Δθ)`. -/
noncomputable def deltaw (K : Matrix n n 𝕜) (J : Matrix n p 𝕜) (H : Matrix p p 𝕜)
    (rw : n → 𝕜) (rθ : p → 𝕜) : n → 𝕜 :=
  -(K⁻¹ *ᵥ (rw + J *ᵥ deltaθ K J H rw rθ))

/--
**Cross-stage solve.** When the Riccati block `K` and the dense Schur
complement `S_θ = H - J_θᵀ K⁻¹ J_θ` are invertible, the pair `(Δw, Δθ)` defined
by `deltaw`/`deltaθ` solves the arrowhead Newton system

```
  [ K    J_θ ] [ Δw ]      [ r_w ]
  [ J_θᵀ H   ] [ Δθ ]  = - [ r_θ ].
```
-/
theorem crossStage_schur_solve
    (K : Matrix n n 𝕜) (J : Matrix n p 𝕜) (H : Matrix p p 𝕜)
    (rw : n → 𝕜) (rθ : p → 𝕜)
    (hK : IsUnit K.det) (hS : IsUnit (schurθ K J H).det) :
    (fromBlocks K J Jᵀ H) *ᵥ
        (Sum.elim (deltaw K J H rw rθ) (deltaθ K J H rw rθ))
      = Sum.elim (-rw) (-rθ) := by
  simp +decide only [deltaw, deltaθ, schurθ];
  ext i;
  cases i <;> simp +decide [ Matrix.fromBlocks_mulVec, Matrix.mulVec_add, Matrix.mulVec_neg, Matrix.mulVec_mulVec ];
  · simp_all +decide [ Matrix.mul_assoc, isUnit_iff_ne_zero ];
  · have := Matrix.mul_nonsing_inv ( H - Jᵀ * K⁻¹ * J ) hS;
    replace this := congr_arg ( fun m => m *ᵥ ( rθ - ( Jᵀ * K⁻¹ ) *ᵥ rw ) ) this ; simp_all +decide [ Matrix.mul_assoc ] ;
    simp_all +decide [ Matrix.sub_mul, Matrix.mul_assoc, Matrix.sub_mulVec ];
    replace this := congr_fun this ‹_›; norm_num at *; linear_combination -this;

end CrossStageVariables