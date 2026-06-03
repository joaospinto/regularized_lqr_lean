/-
# Descent Direction Theorem (Theorem 1 of the paper)

This file proves the full descent direction theorem (Theorem 1) from
"Dual-Regularized Riccati Recursions for Interior-Point Optimal Control"
(Sousa-Pinto & Orban).

## Main result

`augmented_lagrangian_descent` (Theorem 1): Given the KKT system of the
regularized interior point method, the directional derivative of the
Augmented Barrier-Lagrangian along the primal search direction (Δx, Δs)
is strictly negative whenever (Δx, Δs) ≠ 0.

The KKT system is:
  P Δx + Cᵀ Δỹ + Gᵀ Δz̃ = -∇ₓ A
  W⁻¹ Δs         + Δz̃ = -∇ₛ A
             Δỹ = Δ_C (C Δx)
             Δz̃ = Δ_G (G Δx + Δs)

## Proof outline

1. Express the directional derivative as grad_x ⋅ Δx + grad_s ⋅ Δs.
2. Substitute the KKT equations to rewrite this as the negative of
   ‖Δx‖²_P + ‖Δs‖²_{W⁻¹} + ‖CΔx‖²_{Δ_C} + ‖GΔx + Δs‖²_{Δ_G}.
3. This sum is strictly positive by positive definiteness of P, W⁻¹, Δ_C, Δ_G.

The variables Δx, Δs may live in different-dimensional spaces (Fin nx, Fin ns),
and the constraint Jacobians C, G are rectangular.
-/
import Mathlib

set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false

open Matrix

variable {n : ℕ} [DecidableEq (Fin n)]

/-- Key algebraic identity: xᵀAᵀy = yᵀAx via dotProduct and mulVec. -/
theorem dotProduct_mulVec_transpose
    (A : Matrix (Fin n) (Fin n) ℝ) (x y : Fin n → ℝ) :
    dotProduct x (Aᵀ.mulVec y) = dotProduct y (A.mulVec x) := by
  simp +decide [ Matrix.mulVec, dotProduct ];
  simpa only [ Finset.mul_sum _ _ _, mul_assoc, mul_comm, mul_left_comm ] using Finset.sum_comm

/-- The cross terms in the directional derivative reduce to squared norms:
    dxᵀ Cᵀ (Δ_C C dx) + dxᵀ Gᵀ (Δ_G (G dx + ds)) + dsᵀ (Δ_G (G dx + ds))
    = (C dx)ᵀ Δ_C (C dx) + (G dx + ds)ᵀ Δ_G (G dx + ds) -/
theorem descent_cross_terms
    {C G DeltaC DeltaG : Matrix (Fin n) (Fin n) ℝ}
    (dx ds : Fin n → ℝ) :
    dotProduct dx (Cᵀ.mulVec (DeltaC.mulVec (C.mulVec dx)))
    + dotProduct dx (Gᵀ.mulVec (DeltaG.mulVec (G.mulVec dx + ds)))
    + dotProduct ds (DeltaG.mulVec (G.mulVec dx + ds))
    = dotProduct (C.mulVec dx) (DeltaC.mulVec (C.mulVec dx))
    + dotProduct (G.mulVec dx + ds) (DeltaG.mulVec (G.mulVec dx + ds)) := by
  norm_num [ Matrix.mul_apply, dotProduct_comm ] at * ; ring_nf at *;
  simp_all +decide [ Matrix.vecMul_mulVec, Matrix.dotProduct_mulVec, dotProduct_comm ] ; ring_nf at *;

/-- PosDef matrices give strictly positive quadratic forms on nonzero vectors. -/
theorem posDef_dotProduct_pos
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef)
    {x : Fin n → ℝ} (hx : x ≠ 0) :
    0 < dotProduct x (A.mulVec x) := by
  have h_pos : ∀ (v : Fin n → ℝ), v ≠ 0 → 0 < dotProduct v (A.mulVec v) := by
    intro v hv
    have := hA.2
    simp_all +decide [ dotProduct, Matrix.mulVec ];
    convert this ( show ( Finsupp.equivFunOnFinite.symm v ) ≠ 0 from fun h => hv <| by simpa using congr_arg ( fun f => Finsupp.equivFunOnFinite f ) h ) using 1 ; simp +decide [ Finsupp.sum_fintype, mul_comm, mul_left_comm, Finset.mul_sum _ _ _ ];
  exact h_pos x hx

/-- PosDef matrices give nonneg quadratic forms. -/
theorem posDef_dotProduct_nonneg
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef)
    (x : Fin n → ℝ) :
    0 ≤ dotProduct x (A.mulVec x) := by
  by_cases hx : x = 0;
  · simp +decide [ hx ];
  · exact le_of_lt ( posDef_dotProduct_pos hA hx )

/-- **Strict positivity of sum of quadratic forms**: When P, W⁻¹, Δ_C, Δ_G are
    positive definite, the sum ‖Δx‖²_P + ‖Δs‖²_{W⁻¹} + ‖CΔx‖²_{Δ_C} + ‖GΔx + Δs‖²_{Δ_G}
    is strictly positive whenever (Δx, Δs) ≠ 0.

    This is the algebraic core of Theorem 1 in the paper. The full theorem
    additionally requires showing that the directional derivative of the
    Augmented Barrier-Lagrangian equals the negative of this sum (not formalized). -/
theorem descent_direction_neg
    {P Winv C G DeltaC DeltaG : Matrix (Fin n) (Fin n) ℝ}
    (hP : P.PosDef) (hW : Winv.PosDef)
    (hDC : DeltaC.PosDef) (hDG : DeltaG.PosDef)
    (dx ds : Fin n → ℝ) (h : dx ≠ 0 ∨ ds ≠ 0) :
    dotProduct dx (P.mulVec dx) + dotProduct ds (Winv.mulVec ds)
    + dotProduct (C.mulVec dx) (DeltaC.mulVec (C.mulVec dx))
    + dotProduct (G.mulVec dx + ds) (DeltaG.mulVec (G.mulVec dx + ds)) > 0 := by
  have hDCnn := posDef_dotProduct_nonneg hDC (C.mulVec dx)
  have hDGnn := posDef_dotProduct_nonneg hDG (G.mulVec dx + ds)
  rcases h with hdx | hds
  · have hPpos := posDef_dotProduct_pos hP hdx
    have hWnn := posDef_dotProduct_nonneg hW ds
    linarith
  · have hPnn := posDef_dotProduct_nonneg hP dx
    have hWpos := posDef_dotProduct_pos hW hds
    linarith

-- ═══════════════════════════════════════════════════════════════════════════
-- § 2. Full Descent Direction Theorem (Theorem 1)
-- ═══════════════════════════════════════════════════════════════════════════

/-! ### Multi-dimensional setting

The full theorem allows Δx ∈ ℝⁿˣ and Δs ∈ ℝⁿˢ to live in different spaces,
with rectangular constraint Jacobians C : nc × nx and G : ns × nx. -/

variable {nx ns nc : ℕ} [DecidableEq (Fin nx)] [DecidableEq (Fin ns)] [DecidableEq (Fin nc)]

/-- PosDef matrices give strictly positive quadratic forms on nonzero vectors.
    (Multi-dimensional version for index type `Fin k`.) -/
theorem posDef_dotProduct_pos' {k : ℕ} [DecidableEq (Fin k)]
    {A : Matrix (Fin k) (Fin k) ℝ} (hA : A.PosDef)
    {x : Fin k → ℝ} (hx : x ≠ 0) :
    0 < dotProduct x (A.mulVec x) :=
  posDef_dotProduct_pos hA hx

/-- PosDef matrices give nonneg quadratic forms.
    (Multi-dimensional version for index type `Fin k`.) -/
theorem posDef_dotProduct_nonneg' {k : ℕ} [DecidableEq (Fin k)]
    {A : Matrix (Fin k) (Fin k) ℝ} (hA : A.PosDef)
    (x : Fin k → ℝ) :
    0 ≤ dotProduct x (A.mulVec x) :=
  posDef_dotProduct_nonneg hA x

/-
**Theorem 1 (Descent Direction — Full Statement)**.

Given the KKT system of the regularized interior point method:
```
  P Δx + Cᵀ Δỹ + Gᵀ Δz̃ = -grad_x
  W⁻¹ Δs       + Δz̃ = -grad_s
  Δỹ = Δ_C (C Δx)
  Δz̃ = Δ_G (G Δx + Δs)
```

where P, W⁻¹, Δ_C, Δ_G are positive definite, the directional derivative
of the Augmented Barrier-Lagrangian along (Δx, Δs) is:

  D(A; (Δx, Δs)) = grad_x ⬝ Δx + grad_s ⬝ Δs < 0

whenever (Δx, Δs) ≠ 0.

This is the content of Theorem 1 from "Dual-Regularized Riccati Recursions
for Interior-Point Optimal Control" (Sousa-Pinto & Orban).
-/
theorem augmented_lagrangian_descent
    {P : Matrix (Fin nx) (Fin nx) ℝ}
    {Winv : Matrix (Fin ns) (Fin ns) ℝ}
    {C : Matrix (Fin nc) (Fin nx) ℝ}
    {G : Matrix (Fin ns) (Fin nx) ℝ}
    {DeltaC : Matrix (Fin nc) (Fin nc) ℝ}
    {DeltaG : Matrix (Fin ns) (Fin ns) ℝ}
    (hP : P.PosDef) (hW : Winv.PosDef)
    (hDC : DeltaC.PosDef) (hDG : DeltaG.PosDef)
    {dx : Fin nx → ℝ} {ds : Fin ns → ℝ}
    {grad_x : Fin nx → ℝ} {grad_s : Fin ns → ℝ}
    {dy_tilde : Fin nc → ℝ} {dz_tilde : Fin ns → ℝ}
    -- KKT row 1: P Δx + Cᵀ Δỹ + Gᵀ Δz̃ = -grad_x
    (hKKT1 : P.mulVec dx + Cᵀ.mulVec dy_tilde + Gᵀ.mulVec dz_tilde = -grad_x)
    -- KKT row 2: W⁻¹ Δs + Δz̃ = -grad_s
    (hKKT2 : Winv.mulVec ds + dz_tilde = -grad_s)
    -- KKT row 3: Δỹ = Δ_C (C Δx)
    (hKKT3 : dy_tilde = DeltaC.mulVec (C.mulVec dx))
    -- KKT row 4: Δz̃ = Δ_G (G Δx + Δs)
    (hKKT4 : dz_tilde = DeltaG.mulVec (G.mulVec dx + ds))
    -- Nontrivial direction
    (h : dx ≠ 0 ∨ ds ≠ 0) :
    dotProduct grad_x dx + dotProduct grad_s ds < 0 := by
  -- By definition of $h$, we know that either $dx \neq 0$ or $ds \neq 0$.
  by_cases h_dx : dx ≠ 0;
  · have h_neg : -dotProduct dx (P.mulVec dx) - dotProduct dx (Cᵀ.mulVec (DeltaC.mulVec (C.mulVec dx))) - dotProduct dx (Gᵀ.mulVec (DeltaG.mulVec (G.mulVec dx + ds))) - dotProduct ds (Winv.mulVec ds) - dotProduct ds (DeltaG.mulVec (G.mulVec dx + ds)) < 0 := by
      have h_neg : -dotProduct dx (P.mulVec dx) - dotProduct (C.mulVec dx) (DeltaC.mulVec (C.mulVec dx)) - dotProduct (G.mulVec dx + ds) (DeltaG.mulVec (G.mulVec dx + ds)) - dotProduct ds (Winv.mulVec ds) < 0 := by
        have h_neg : -dotProduct dx (P.mulVec dx) < 0 := by
          exact neg_neg_of_pos ( posDef_dotProduct_pos' hP h_dx );
        linarith [ posDef_dotProduct_nonneg' hDC ( C.mulVec dx ), posDef_dotProduct_nonneg' hDG ( G.mulVec dx + ds ), posDef_dotProduct_nonneg' hW ds ];
      convert h_neg using 1 ; norm_num [ Matrix.dotProduct_mulVec, Matrix.vecMul_transpose ] ; ring;
      simp +decide [ Matrix.vecMul_add, Matrix.add_vecMul, Matrix.mul_assoc, Matrix.dotProduct_mulVec, Matrix.vecMul_mulVec ] ; ring;
    convert h_neg using 1;
    rw [ ← eq_sub_iff_add_eq' ] at * ; simp_all +decide [ Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add, dotProduct_smul ] ; ring;
    simp +decide [ dotProduct_comm ];
  · simp_all +decide [ Matrix.mulVec, dotProduct ];
    -- By definition of $h$, we know that $ds \neq 0$.
    have h_ds : 0 < dotProduct ds (Winv.mulVec ds) + dotProduct ds (DeltaG.mulVec ds) := by
      exact add_pos_of_nonneg_of_pos ( posDef_dotProduct_nonneg' hW ds ) ( posDef_dotProduct_pos' hDG h );
    simp_all +decide [ ← eq_sub_iff_add_eq', dotProduct_add, dotProduct_smul ];
    simpa only [ dotProduct, mul_comm ] using h_ds