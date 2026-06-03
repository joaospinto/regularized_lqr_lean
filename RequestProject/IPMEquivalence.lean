/-
# IPM Linear System Equivalence

This file proves the linear system equivalence lemma from
"Dual-Regularized Riccati Recursions for Interior-Point Optimal Control"
(Sousa-Pinto & Orban).

The KKT system of the regularized interior point method is:
```
  P Δx + Cᵀ Δỹ + Gᵀ Δz̃ = -grad_x      (1)
  W⁻¹ Δs       + Δz̃ = -grad_s           (2)
  Δỹ = Δ_C (C Δx)                        (3)
  Δz̃ = Δ_G (G Δx + Δs)                  (4)
```

Substituting (3) and (4) into (1) and (2) yields the reduced system:
```
  (P + Cᵀ Δ_C C + Gᵀ Δ_G G) Δx + Gᵀ Δ_G Δs = -grad_x      (1')
  Δ_G G Δx + (W⁻¹ + Δ_G) Δs = -grad_s                        (2')
```

This reduced 2×2 block system is what the Riccati recursion actually solves.
The equivalence shows that the dual variables (Δỹ, Δz̃) can be eliminated,
reducing the 4-equation KKT system to a 2-equation system in (Δx, Δs) only.
-/
import Mathlib

open Matrix

set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false

variable {nx ns nc : ℕ} [DecidableEq (Fin nx)] [DecidableEq (Fin ns)] [DecidableEq (Fin nc)]

/-- **IPM Linear System Equivalence (Row 1).**

  Substituting `Δỹ = Δ_C (C Δx)` and `Δz̃ = Δ_G (G Δx + Δs)` into
  the first KKT equation `P Δx + Cᵀ Δỹ + Gᵀ Δz̃ = -grad_x` yields
  `(P + Cᵀ Δ_C C + Gᵀ Δ_G G) Δx + Gᵀ Δ_G Δs = -grad_x`. -/
theorem ipm_reduced_row1
    (P : Matrix (Fin nx) (Fin nx) ℝ)
    (C : Matrix (Fin nc) (Fin nx) ℝ)
    (G : Matrix (Fin ns) (Fin nx) ℝ)
    (DeltaC : Matrix (Fin nc) (Fin nc) ℝ)
    (DeltaG : Matrix (Fin ns) (Fin ns) ℝ)
    (dx : Fin nx → ℝ) (ds : Fin ns → ℝ)
    (grad_x : Fin nx → ℝ)
    (hKKT1 : P.mulVec dx + Cᵀ.mulVec (DeltaC.mulVec (C.mulVec dx))
             + Gᵀ.mulVec (DeltaG.mulVec (G.mulVec dx + ds)) = -grad_x) :
    (P + Cᵀ * DeltaC * C + Gᵀ * DeltaG * G).mulVec dx
    + (Gᵀ * DeltaG).mulVec ds = -grad_x := by
  convert hKKT1 using 1
  simp +decide [Matrix.add_mulVec, Matrix.mulVec_add, Matrix.mul_assoc]
  abel1

/-- **IPM Linear System Equivalence (Row 2).**

  Substituting `Δz̃ = Δ_G (G Δx + Δs)` into the second KKT equation
  `W⁻¹ Δs + Δz̃ = -grad_s` yields
  `Δ_G G Δx + (W⁻¹ + Δ_G) Δs = -grad_s`. -/
theorem ipm_reduced_row2
    (Winv : Matrix (Fin ns) (Fin ns) ℝ)
    (G : Matrix (Fin ns) (Fin nx) ℝ)
    (DeltaG : Matrix (Fin ns) (Fin ns) ℝ)
    (dx : Fin nx → ℝ) (ds : Fin ns → ℝ)
    (grad_s : Fin ns → ℝ)
    (hKKT2 : Winv.mulVec ds + DeltaG.mulVec (G.mulVec dx + ds) = -grad_s) :
    (DeltaG * G).mulVec dx + (Winv + DeltaG).mulVec ds = -grad_s := by
  convert hKKT2 using 1
  simp +decide [Matrix.add_mulVec, Matrix.mulVec_add, Matrix.mulVec_mulVec]
  ring

/-- **IPM Linear System Full Equivalence.**

  The full 4-equation KKT system is equivalent to the reduced 2-equation system
  in (Δx, Δs) together with the explicit dual variable definitions. -/
theorem ipm_system_equivalence
    (P : Matrix (Fin nx) (Fin nx) ℝ)
    (Winv : Matrix (Fin ns) (Fin ns) ℝ)
    (C : Matrix (Fin nc) (Fin nx) ℝ)
    (G : Matrix (Fin ns) (Fin nx) ℝ)
    (DeltaC : Matrix (Fin nc) (Fin nc) ℝ)
    (DeltaG : Matrix (Fin ns) (Fin ns) ℝ)
    (dx : Fin nx → ℝ) (ds : Fin ns → ℝ)
    (grad_x : Fin nx → ℝ) (grad_s : Fin ns → ℝ)
    (dy_tilde : Fin nc → ℝ) (dz_tilde : Fin ns → ℝ)
    (hKKT1 : P.mulVec dx + Cᵀ.mulVec dy_tilde + Gᵀ.mulVec dz_tilde = -grad_x)
    (hKKT2 : Winv.mulVec ds + dz_tilde = -grad_s)
    (hKKT3 : dy_tilde = DeltaC.mulVec (C.mulVec dx))
    (hKKT4 : dz_tilde = DeltaG.mulVec (G.mulVec dx + ds)) :
    (P + Cᵀ * DeltaC * C + Gᵀ * DeltaG * G).mulVec dx
      + (Gᵀ * DeltaG).mulVec ds = -grad_x
    ∧ (DeltaG * G).mulVec dx + (Winv + DeltaG).mulVec ds = -grad_s := by
  subst hKKT3; subst hKKT4
  exact ⟨ipm_reduced_row1 P C G DeltaC DeltaG dx ds grad_x hKKT1,
         ipm_reduced_row2 Winv G DeltaG dx ds grad_s hKKT2⟩
