/-
# Associativity of the IVF Combination Rule

This file proves that `ivfCombine` is associative, which is the key property
enabling parallelization via Blelloch-style associative (prefix) scans.

## Main Result

`ivfCombine_assoc`: For interval value functions L, M, R (with symmetric
P and C components), ivfCombine (ivfCombine L M) R = ivfCombine L (ivfCombine M R)

## Symmetry Requirement

The P and C components of each IVF must be symmetric. This always holds in
the dual-regularized LQR application:
- P is the cost-to-go Hessian (symmetric by definition of quadratic form)
- C is the augmented regularization Δ + BR⁻¹Bᵀ (symmetric by construction)

## One-Inverse Optimization

We also prove `ivfCombine_P_one_inverse`: the P formula can be
computed using a single matrix factorization (I + C₁ P₂)⁻¹ instead of
two separate inverses.

References:
- Deng & Bhatt, arXiv:2104.03186 (combination rules)
- Blelloch, "Prefix Sums and Their Applications" (parallel scan)
-/
import Mathlib
import RequestProject.ParallelRiccati
import RequestProject.MatrixHelpers

open Matrix

set_option maxHeartbeats 3200000

variable {n : ℕ} [DecidableEq (Fin n)]

-- ═══════════════════════════════════════════════════════════════════════════
-- § 0. Extensionality for IntervalValueFn
-- ═══════════════════════════════════════════════════════════════════════════

@[ext]
theorem IntervalValueFn.ext' {n : ℕ} {a b : IntervalValueFn n}
    (hP : a.P = b.P) (hp : a.p = b.p) (hA : a.Amat = b.Amat)
    (hC : a.C = b.C) (hc : a.cvec = b.cvec) : a = b := by
  cases a; cases b; simp_all

-- ═══════════════════════════════════════════════════════════════════════════
-- § 1. One-Inverse Optimization
-- ═══════════════════════════════════════════════════════════════════════════

/-- The P component of ivfCombine can be computed using only (I + C₁ P₂)⁻¹
    instead of (I + P₂ C₁)⁻¹, via the identity (I+PC)⁻¹ P = P (I+CP)⁻¹. -/
theorem ivfCombine_P_one_inverse (left right : IntervalValueFn n)
    (hF1 : IsUnit (1 + right.P * left.C))
    (hF2 : IsUnit (1 + left.C * right.P)) :
    (ivfCombine left right).P =
    left.Amatᵀ * right.P * (1 + left.C * right.P)⁻¹ * left.Amat + left.P := by
  unfold ivfCombine; simp only []
  congr 1
  have h := inv_mul_comm left.C right.P hF1 hF2
  calc left.Amatᵀ * (1 + right.P * left.C)⁻¹ * right.P * left.Amat
      = left.Amatᵀ * ((1 + right.P * left.C)⁻¹ * right.P) * left.Amat := by
        simp [Matrix.mul_assoc]
    _ = left.Amatᵀ * (right.P * (1 + left.C * right.P)⁻¹) * left.Amat := by rw [h]
    _ = left.Amatᵀ * right.P * (1 + left.C * right.P)⁻¹ * left.Amat := by
        simp [Matrix.mul_assoc]

-- ═══════════════════════════════════════════════════════════════════════════
-- § 2. Hypotheses Bundle for Associativity
-- ═══════════════════════════════════════════════════════════════════════════

/-- Bundle of invertibility and symmetry hypotheses for three-way IVF
    combination. The symmetry conditions always hold in the LQR application
    (P = Hessian, C = regularization). -/
structure IVFAssocHyp (L M R : IntervalValueFn n) where
  /-- Symmetry of P and C for each IVF -/
  hLP : L.P.IsSymm
  hLC : L.C.IsSymm
  hMP : M.P.IsSymm
  hMC : M.C.IsSymm
  hRP : R.P.IsSymm
  hRC : R.C.IsSymm
  /-- Invertibility for combining L ⊕ M -/
  hLM_1 : IsUnit (1 + M.P * L.C)
  hLM_2 : IsUnit (1 + L.C * M.P)
  /-- Invertibility for combining M ⊕ R -/
  hMR_1 : IsUnit (1 + R.P * M.C)
  hMR_2 : IsUnit (1 + M.C * R.P)
  /-- Invertibility for combining (L⊕M) ⊕ R -/
  hLMR_1 : IsUnit (1 + R.P * (ivfCombine L M).C)
  hLMR_2 : IsUnit (1 + (ivfCombine L M).C * R.P)
  /-- Invertibility for combining L ⊕ (M⊕R) -/
  hLMR_3 : IsUnit (1 + (ivfCombine M R).P * L.C)
  hLMR_4 : IsUnit (1 + L.C * (ivfCombine M R).P)

-- ═══════════════════════════════════════════════════════════════════════════
-- § 3. Symmetry preservation
-- ═══════════════════════════════════════════════════════════════════════════

/-- When P and C are symmetric, (1+CP)⁻¹ᵀ = (1+PC)⁻¹. -/
theorem inv_transpose_symm (P C : Matrix (Fin n) (Fin n) ℝ)
    (hP : P.IsSymm) (hC : C.IsSymm) :
    ((1 + C * P)⁻¹)ᵀ = (1 + P * C)⁻¹ := by
  rw [Matrix.transpose_nonsing_inv]
  congr 1
  rw [Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_mul, hP, hC]

/-
═══════════════════════════════════════════════════════════════════════════
§ 4. Push-through resolvent identity
═══════════════════════════════════════════════════════════════════════════

**Push-through identity for nested resolvents.**
-/
theorem pushthrough_resolvent
    (A C P D Q : Matrix (Fin n) (Fin n) ℝ)
    (hCP : IsUnit (1 + C * P))
    (hPC : IsUnit (1 + P * C))
    (hDQ : IsUnit (1 + D * Q))
    (hQD : IsUnit (1 + Q * D))
    (hLHS : IsUnit (1 + (A * (1 + C * P)⁻¹ * C * Aᵀ + D) * Q))
    (hRHS : IsUnit (1 + C * (Aᵀ * (1 + Q * D)⁻¹ * Q * A + P))) :
    (1 + (A * (1 + C * P)⁻¹ * C * Aᵀ + D) * Q)⁻¹ *
      A * (1 + C * P)⁻¹ =
    (1 + D * Q)⁻¹ * A *
      (1 + C * (Aᵀ * (1 + Q * D)⁻¹ * Q * A + P))⁻¹ := by
  simp_all +decide [ mul_assoc, mul_left_comm, Matrix.isUnit_iff_isUnit_det ];
  have h_mul : (1 + (A * ((1 + C * P)⁻¹ * (C * Aᵀ)) + D) * Q) * ((1 + D * Q)⁻¹ * A * (1 + C * (Aᵀ * ((1 + Q * D)⁻¹ * (Q * A)) + P))⁻¹) = A * (1 + C * P)⁻¹ := by
    have h_mul : (1 + (A * ((1 + C * P)⁻¹ * (C * Aᵀ)) + D) * Q) * ((1 + D * Q)⁻¹ * A) = A * (1 + C * P)⁻¹ * (1 + C * (Aᵀ * ((1 + Q * D)⁻¹ * (Q * A)) + P)) := by
      simp +decide [ mul_add, add_mul, mul_assoc, mul_left_comm, hDQ, hQD, hCP, hPC ];
      have h_mul : Q * ((1 + D * Q)⁻¹ * A) = ((1 + Q * D)⁻¹ * Q) * A := by
        simp +decide [ ← mul_assoc, ← Matrix.mul_inv_rev, hDQ, hQD ];
        have h_simp : Q * (1 + D * Q)⁻¹ = (1 + Q * D)⁻¹ * Q := by
          have h_eq : (1 + Q * D) * Q = Q * (1 + D * Q) := by
            simp +decide [ mul_add, add_mul, mul_assoc ]
          apply_fun ( fun x => ( 1 + Q * D ) ⁻¹ * x * ( 1 + D * Q ) ⁻¹ ) at h_eq ; simp_all +decide [ Matrix.mul_assoc ];
        rw [h_simp];
      have h_mul : (1 + D * Q)⁻¹ = 1 - D * (1 + Q * D)⁻¹ * Q := by
        have h_mul : (1 + D * Q) * (1 - D * (1 + Q * D)⁻¹ * Q) = 1 := by
          simp +decide [ mul_sub, sub_mul, mul_assoc, hQD, isUnit_iff_ne_zero ];
          simp +decide [ mul_assoc, add_mul, mul_add, hQD, isUnit_iff_ne_zero ];
          simp +decide [ ← mul_assoc, ← add_mul, hQD, isUnit_iff_ne_zero ];
          rw [ show D + D * Q * D = D * ( 1 + Q * D ) by simp +decide [ mul_add, add_mul, mul_assoc ] ] ; simp +decide [ mul_assoc, hQD, isUnit_iff_ne_zero ];
        rw [ Matrix.inv_eq_right_inv h_mul ];
      simp_all +decide [ mul_assoc, sub_mul, mul_sub ];
      simp +decide [ mul_add, add_assoc, add_comm, add_left_comm, hCP, hPC, hDQ, hQD, isUnit_iff_ne_zero ];
      rw [ show ( C * P + 1 ) ⁻¹ * ( C * P ) = 1 - ( C * P + 1 ) ⁻¹ from ?_ ] ; simp +decide [ mul_sub, sub_mul, mul_assoc, mul_left_comm, hCP, hPC, hDQ, hQD, isUnit_iff_ne_zero ] ; abel_nf;
      have h_mul : (C * P + 1)⁻¹ * (C * P + 1) = 1 := by
        rw [ Matrix.nonsing_inv_mul _ ];
        exact isUnit_iff_ne_zero.mpr ( by simpa only [ add_comm ] using hCP );
      simp_all +decide [ mul_add, add_mul, mul_assoc, mul_left_comm, sub_eq_add_neg ];
      exact eq_add_neg_of_add_eq h_mul;
    simp_all +decide [ ← mul_assoc ];
  simp +decide [ ← h_mul, mul_assoc, hLHS ]

/-
═══════════════════════════════════════════════════════════════════════════
§ 5. Associativity — Component-wise
═══════════════════════════════════════════════════════════════════════════

Associativity of the A (coupling matrix) component.
-/
theorem ivfCombine_assoc_Amat (L M R : IntervalValueFn n)
    (h : IVFAssocHyp L M R) :
    (ivfCombine (ivfCombine L M) R).Amat =
    (ivfCombine L (ivfCombine M R)).Amat := by
  have := @pushthrough_resolvent;
  convert congr_arg ( fun x => R.Amat * x * L.Amat ) ( this M.Amat L.C M.P M.C R.P h.hLM_2 h.hLM_1 h.hMR_2 h.hMR_1 h.hLMR_2 h.hLMR_4 ) using 1 ; simp +decide [ Matrix.mul_assoc ];
  · -- By definition of ivfCombine, the Amat of the combined system is R.Amat multiplied by the product of the inverses and matrices.
    simp [ivfCombine];
    simp +decide only [Matrix.mul_assoc];
  · unfold ivfCombine; simp +decide [ Matrix.mul_assoc ] ;

/-
Helper: For symmetric P₂₃ and C, (1+P₂₃*C)⁻¹ is the transpose of (1+C*P₂₃)⁻¹.
    Combined with F₂ᵀ = (1+P*C)⁻¹ and the identity (1+P₂₃*C)*(inner) = P₂₃,
    this yields the P component associativity.

    Specifically: F'ᵀ * S * F₂ + P * F₂ = P₂₃ * F'
    where P₂₃ = S + P, F₂ = (1+CP)⁻¹, F' = (1+C*P₂₃)⁻¹.

    Proof: Left-multiply by (1+P₂₃*C) = F'ᵀ⁻¹:
    S*F₂ + (1+P₂₃*C)*P*F₂ = S*F₂ + (1+(S+P)*C)*P*F₂
    = S*F₂ + P*F₂ + (S+P)*C*P*F₂ = (S+P)*(1+CP)*F₂ = P₂₃
-/
theorem P_component_identity
    (S P C : Matrix (Fin n) (Fin n) ℝ)
    (hCP : IsUnit (1 + C * P))
    (hPC : IsUnit (1 + P * C))
    (hSPC : IsUnit (1 + C * (S + P)))
    (hSCP : IsUnit (1 + (S + P) * C))
    (hPs : P.IsSymm) (hCs : C.IsSymm) (hSs : S.IsSymm) :
    ((1 + C * (S + P))⁻¹)ᵀ * S * (1 + C * P)⁻¹ + P * (1 + C * P)⁻¹ =
    (S + P) * (1 + C * (S + P))⁻¹ := by
  have hF'_inv : (1 + (S + P) * C) * (1 + C * (S + P))⁻¹ᵀ = 1 := by
    have hF'_inv : (1 + C * (S + P))⁻¹ᵀ = (1 + (S + P) * C)⁻¹ := by
      convert inv_transpose_symm _ _ _ _ using 1 <;> simp_all +decide [ Matrix.IsSymm ];
    rw [ hF'_inv, Matrix.mul_nonsing_inv _ ];
    exact IsUnit.map ( Matrix.detMonoidHom ) hSCP;
  have hF'_inv : (1 + (S + P) * C) * ((1 + C * (S + P))⁻¹ᵀ * S * (1 + C * P)⁻¹ + P * (1 + C * P)⁻¹) = (S + P) := by
    simp_all +decide [ mul_add, add_mul, ← mul_assoc ];
    have hF'_inv : (1 + C * P) * (1 + C * P)⁻¹ = 1 := by
      exact Matrix.mul_nonsing_inv _ ( show IsUnit ( 1 + C * P |> Matrix.det ) from hCP.map ( Matrix.detMonoidHom ) );
    convert congr_arg ( fun x => S * x + P * x ) hF'_inv using 1 <;> simp +decide [ mul_add, add_mul, mul_assoc, add_assoc, add_left_comm, add_comm ];
  convert congr_arg ( fun x => ( 1 + ( S + P ) * C ) ⁻¹ * x ) hF'_inv using 1;
  · rw [ ← mul_assoc, Matrix.nonsing_inv_mul _ ];
    · rw [ one_mul ];
    · exact IsUnit.map ( Matrix.detMonoidHom ) hSCP;
  · rw [ ← mul_eq_one_comm ] at *;
    exact?

/-
Associativity of the P (Hessian) component.
-/
theorem ivfCombine_assoc_P (L M R : IntervalValueFn n)
    (h : IVFAssocHyp L M R) :
    (ivfCombine (ivfCombine L M) R).P =
    (ivfCombine L (ivfCombine M R)).P := by
  have := h;
  revert this;
  revert h;
  intro h1 h2
  have h3 := h1.hLM_1
  have h4 := h1.hLM_2
  have h5 := h1.hMR_1
  have h6 := h1.hMR_2
  have h7 := h1.hLMR_1
  have h8 := h1.hLMR_2
  have h9 := h1.hLMR_3
  have h10 := h1.hLMR_4
  simp_all +decide [ ivfCombine ];
  convert congr_arg ( fun x => L.Amatᵀ * x * L.Amat + L.P ) ( P_component_identity ( M.Amatᵀ * ( 1 + R.P * M.C ) ⁻¹ * R.P * M.Amat ) M.P L.C _ _ _ _ _ _ _ ) using 1 <;> norm_num [ h3, h4, h5, h6, h7, h8, h9, h10 ];
  · have := pushthrough_resolvent ( M.Amat ) ( L.C ) ( M.P ) ( M.C ) ( R.P ) ; simp_all +decide [ Matrix.mul_assoc, Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul ] ;
    rw [ ← Matrix.transpose_inj ] ; simp_all +decide [ Matrix.mul_assoc, Matrix.transpose_mul, Matrix.transpose_nonsing_inv ] ;
    simp_all +decide [ ← Matrix.mul_assoc, ← eq_sub_iff_add_eq' ];
    rw [ show M.Pᵀ = M.P from h2.hMP, show L.Cᵀ = L.C from h2.hLC, show R.Pᵀ = R.P from h2.hRP, show M.Cᵀ = M.C from h2.hMC ] ; simp_all +decide [ Matrix.mul_assoc, Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul ] ;
    grind +suggestions;
  · grind +suggestions;
  · exact h2.hMP;
  · exact h2.hLC;
  · simp_all +decide [ Matrix.IsSymm, Matrix.mul_assoc ];
    have := h2.hRP; have := h2.hRC; simp_all +decide [ Matrix.IsSymm, Matrix.transpose_nonsing_inv ] ;
    have h_comm : (1 + R.P * M.C)⁻¹ * R.P = R.P * (1 + M.C * R.P)⁻¹ := by
      exact?;
    simp_all +decide [ ← Matrix.mul_assoc ];
    have := h2.hMC; simp_all +decide [ Matrix.IsSymm, Matrix.transpose_nonsing_inv ] ;

/-
Associativity of the C (regularization) component.
-/
theorem ivfCombine_assoc_C (L M R : IntervalValueFn n)
    (h : IVFAssocHyp L M R) :
    (ivfCombine (ivfCombine L M) R).C =
    (ivfCombine L (ivfCombine M R)).C := by
  revert h;
  intro ⟨ hLP, hLC, hMP, hMC, hRP, hRC, hLM_1, hLM_2, hMR_1, hMR_2, hLMR_1, hLMR_2, hLMR_3, hLMR_4 ⟩;
  unfold ivfCombine;
  simp +decide [ Matrix.mul_assoc, Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, Matrix.transpose_mul, Matrix.transpose_add, Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_zero, Matrix.transpose_smul, Matrix.transpose_transpose ] at *;
  rw [ show ( 1 + M.C * R.P ) ⁻¹ᵀ = ( 1 + R.P * M.C ) ⁻¹ from ?_ ];
  · have := pushthrough_resolvent ( M.Amat ) ( L.C ) ( M.P ) ( M.C ) ( R.P ) ?_ ?_ ?_ ?_ ?_ ?_ <;> simp_all +decide [ Matrix.mul_assoc, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, Matrix.transpose_mul, Matrix.transpose_add, Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_zero, Matrix.transpose_smul, Matrix.transpose_transpose ];
    · simp_all +decide [ ← Matrix.mul_assoc, ← eq_sub_iff_add_eq ];
      have h_simp : (1 + (M.Amat * (1 + L.C * M.P)⁻¹ * L.C * M.Amatᵀ * R.P + M.C * R.P))⁻¹ * M.C = (1 + M.C * R.P)⁻¹ * M.C - (1 + (M.Amat * (1 + L.C * M.P)⁻¹ * L.C * M.Amatᵀ * R.P + M.C * R.P))⁻¹ * M.Amat * (1 + L.C * M.P)⁻¹ * L.C * M.Amatᵀ * R.P * (1 + M.C * R.P)⁻¹ * M.C := by
        have h_simp : (1 + (M.Amat * (1 + L.C * M.P)⁻¹ * L.C * M.Amatᵀ * R.P + M.C * R.P))⁻¹ * (1 + M.C * R.P) = 1 - (1 + (M.Amat * (1 + L.C * M.P)⁻¹ * L.C * M.Amatᵀ * R.P + M.C * R.P))⁻¹ * M.Amat * (1 + L.C * M.P)⁻¹ * L.C * M.Amatᵀ * R.P := by
          have h_simp : (1 + (M.Amat * (1 + L.C * M.P)⁻¹ * L.C * M.Amatᵀ * R.P + M.C * R.P))⁻¹ * (1 + (M.Amat * (1 + L.C * M.P)⁻¹ * L.C * M.Amatᵀ * R.P + M.C * R.P)) = 1 := by
            rw [ Matrix.nonsing_inv_mul _ ];
            convert hLMR_2.map ( Matrix.detMonoidHom ) using 1;
            unfold ivfCombine; simp +decide [ Matrix.mul_assoc, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, Matrix.transpose_mul, Matrix.transpose_add, Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_zero, Matrix.transpose_smul, Matrix.transpose_transpose ] ;
          simp_all +decide [ mul_add, add_mul, mul_assoc, add_assoc, add_left_comm, add_comm ];
          grind +splitIndPred;
        convert congr_arg ( fun x => x * ( 1 + M.C * R.P ) ⁻¹ * M.C ) h_simp using 1 <;> simp +decide [ Matrix.mul_assoc, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, Matrix.transpose_mul, Matrix.transpose_add, Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_zero, Matrix.transpose_smul, Matrix.transpose_transpose ];
        cases hMR_2.nonempty_invertible ; aesop;
      simp_all +decide [ Matrix.mul_assoc, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, Matrix.transpose_mul, Matrix.transpose_add, Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_zero, Matrix.transpose_smul, Matrix.transpose_transpose ];
      have h_simp : (1 + R.P * M.C)⁻¹ = 1 - R.P * (1 + M.C * R.P)⁻¹ * M.C := by
        have h_simp : (1 + R.P * M.C) * (1 - R.P * (1 + M.C * R.P)⁻¹ * M.C) = 1 := by
          simp +decide [ mul_sub, sub_mul, ← mul_assoc, hMR_2 ];
          have h_simp : (1 + R.P * M.C) * R.P * (1 + M.C * R.P)⁻¹ = R.P := by
            have h_simp : (1 + R.P * M.C) * R.P = R.P * (1 + M.C * R.P) := by
              simp +decide [ mul_add, add_mul, mul_assoc, hRP.eq ];
            rw [ h_simp, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ ];
            · norm_num;
            · exact IsUnit.map ( Matrix.detMonoidHom ) hMR_2;
          aesop;
        exact Matrix.inv_eq_right_inv h_simp;
      simp +decide [ h_simp, Matrix.mul_assoc, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, Matrix.transpose_mul, Matrix.transpose_add, Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_zero, Matrix.transpose_smul, Matrix.transpose_transpose ];
      abel1;
    · convert hLMR_2 using 1;
      unfold ivfCombine; simp +decide [ Matrix.mul_assoc, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, Matrix.transpose_mul, Matrix.transpose_add, Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_zero, Matrix.transpose_smul, Matrix.transpose_transpose ] ;
    · convert hLMR_4 using 1;
      unfold ivfCombine; simp +decide [ Matrix.mul_assoc, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, Matrix.transpose_mul, Matrix.transpose_add, Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_zero, Matrix.transpose_smul, Matrix.transpose_transpose ] ;
  · grind +suggestions

/-- The pushthrough resolvent applied to vectors via mulVec. -/
theorem pushthrough_resolvent_mulVec
    (A C P D Q : Matrix (Fin n) (Fin n) ℝ)
    (hCP : IsUnit (1 + C * P)) (hPC : IsUnit (1 + P * C))
    (hDQ : IsUnit (1 + D * Q)) (hQD : IsUnit (1 + Q * D))
    (hLHS : IsUnit (1 + (A * (1 + C * P)⁻¹ * C * Aᵀ + D) * Q))
    (hRHS : IsUnit (1 + C * (Aᵀ * (1 + Q * D)⁻¹ * Q * A + P)))
    (v : Fin n → ℝ) :
    ((1 + (A * (1 + C * P)⁻¹ * C * Aᵀ + D) * Q)⁻¹ * A * (1 + C * P)⁻¹).mulVec v =
    ((1 + D * Q)⁻¹ * A * (1 + C * (Aᵀ * (1 + Q * D)⁻¹ * Q * A + P))⁻¹).mulVec v := by
  rw [pushthrough_resolvent A C P D Q hCP hPC hDQ hQD hLHS hRHS]

/-- Helper: P_component_identity applied to vectors via mulVec. -/
theorem P_component_identity_mulVec
    (S P C : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ)
    (hCP : IsUnit (1 + C * P)) (hPC : IsUnit (1 + P * C))
    (hSPC : IsUnit (1 + C * (S + P))) (hSCP : IsUnit (1 + (S + P) * C))
    (hPs : P.IsSymm) (hCs : C.IsSymm) (hSs : S.IsSymm) :
    ((1 + C * (S + P))⁻¹)ᵀ.mulVec (S.mulVec ((1 + C * P)⁻¹.mulVec v)) +
    P.mulVec ((1 + C * P)⁻¹.mulVec v) =
    (S + P).mulVec ((1 + C * (S + P))⁻¹.mulVec v) := by
  have h := P_component_identity S P C hCP hPC hSPC hSCP hPs hCs hSs
  have : (((1 + C * (S + P))⁻¹)ᵀ * S * (1 + C * P)⁻¹ + P * (1 + C * P)⁻¹).mulVec v =
    ((S + P) * (1 + C * (S + P))⁻¹).mulVec v := by rw [h]
  simp [← Matrix.mulVec_mulVec, Matrix.add_mulVec, Matrix.add_mulVec] at this ⊢
  exact this

/-
Symmetry of the Schur complement A*(1+CP)⁻¹*C*Aᵀ when P and C are symmetric.
-/
theorem schur_symm (A C P : Matrix (Fin n) (Fin n) ℝ)
    (hCP : IsUnit (1 + C * P)) (hPC : IsUnit (1 + P * C))
    (hP : P.IsSymm) (hC : C.IsSymm) :
    (A * (1 + C * P)⁻¹ * C * Aᵀ).IsSymm := by
  simp_all +decide [ Matrix.IsSymm, Matrix.mul_assoc ];
  rw [ ← Matrix.mul_assoc, ← Matrix.transpose_inj ] ; simp_all +decide [ Matrix.mul_assoc, Matrix.mul_inv_rev, Matrix.transpose_nonsing_inv ] ;
  grind +suggestions

/-
Symmetry of Aᵀ*(1+QD)⁻¹*Q*A when D and Q are symmetric.
-/
theorem schur_symm' (A D Q : Matrix (Fin n) (Fin n) ℝ)
    (hDQ : IsUnit (1 + D * Q)) (hQD : IsUnit (1 + Q * D))
    (hD : D.IsSymm) (hQ : Q.IsSymm) :
    (Aᵀ * (1 + Q * D)⁻¹ * Q * A).IsSymm := by
  simp_all +decide [ Matrix.IsSymm, mul_assoc ];
  -- Using the fact that $(1 + QD)⁻¹$ is symmetric, we can simplify the expression.
  have h_inv_symm : (1 + Q * D)⁻¹ᵀ = (1 + D * Q)⁻¹ := by
    simp_all +decide [ Matrix.transpose_nonsing_inv ];
  simp_all +decide [ ← mul_assoc, inv_mul_comm ]

/-
The pushthrough resolvent identity, transposed.

From the pushthrough resolvent:
  (1 + (A*(1+CP)⁻¹*C*Aᵀ+D)*Q)⁻¹ * A * (1+CP)⁻¹ = (1+DQ)⁻¹ * A * (1+C*(Aᵀ*(1+QD)⁻¹*Q*A+P))⁻¹

Taking the transpose and using symmetry (P,C,D,Q all symmetric) gives:
  (1+PC)⁻¹ * Aᵀ * (1+Q*(A*(1+CP)⁻¹*C*Aᵀ+D))⁻¹ = (1+(Aᵀ*(1+QD)⁻¹*Q*A+P)*C)⁻¹ * Aᵀ * (1+QD)⁻¹
-/
theorem pushthrough_resolvent_transpose
    (A C P D Q : Matrix (Fin n) (Fin n) ℝ)
    (hCP : IsUnit (1 + C * P))
    (hPC : IsUnit (1 + P * C))
    (hDQ : IsUnit (1 + D * Q))
    (hQD : IsUnit (1 + Q * D))
    (hLHS1 : IsUnit (1 + (A * (1 + C * P)⁻¹ * C * Aᵀ + D) * Q))
    (hLHS2 : IsUnit (1 + Q * (A * (1 + C * P)⁻¹ * C * Aᵀ + D)))
    (hRHS1 : IsUnit (1 + C * (Aᵀ * (1 + Q * D)⁻¹ * Q * A + P)))
    (hRHS2 : IsUnit (1 + (Aᵀ * (1 + Q * D)⁻¹ * Q * A + P) * C))
    (hP : P.IsSymm) (hC : C.IsSymm) (hD : D.IsSymm) (hQ : Q.IsSymm) :
    (1 + P * C)⁻¹ * Aᵀ * (1 + Q * (A * (1 + C * P)⁻¹ * C * Aᵀ + D))⁻¹ =
    (1 + (Aᵀ * (1 + Q * D)⁻¹ * Q * A + P) * C)⁻¹ * Aᵀ * (1 + Q * D)⁻¹ := by
  convert congr_arg Matrix.transpose ( pushthrough_resolvent A C P D Q hCP hPC hDQ hQD hLHS1 hRHS1 ) using 1 <;> simp +decide [ Matrix.mul_assoc, Matrix.transpose_mul ];
  · simp +decide [ Matrix.transpose_nonsing_inv, Matrix.mul_assoc, Matrix.transpose_mul, hP.eq, hC.eq, hD.eq, hQ.eq ];
    have := inv_transpose_symm P C hP hC; simp_all +decide [ Matrix.mul_assoc, Matrix.transpose_mul ] ;
    have := schur_symm A C P hCP hPC hP hC; simp_all +decide [ Matrix.IsSymm, Matrix.mul_assoc ] ;
  · grind +suggestions

/-
Coefficient-of-cvec identity for the p component associativity proof.
    From P_component_identity + push-through:
    (1+(S+P)*C)⁻¹ * S * (1+CP)⁻¹ + (1+PC)⁻¹ * P = (1+(S+P)*C)⁻¹ * (S+P)
-/
lemma p_cvec_coeff
    (S P C : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ)
    (hCP : IsUnit (1 + C * P)) (hPC : IsUnit (1 + P * C))
    (hSPC : IsUnit (1 + C * (S + P))) (hSCP : IsUnit (1 + (S + P) * C))
    (hPs : P.IsSymm) (hCs : C.IsSymm) (hSs : S.IsSymm) :
    ((1 + (S + P) * C)⁻¹ * S * (1 + C * P)⁻¹).mulVec v +
    ((1 + P * C)⁻¹ * P).mulVec v =
    ((1 + (S + P) * C)⁻¹ * (S + P)).mulVec v := by
  convert congr_arg ( fun x => x.mulVec v ) ( P_component_identity S P C hCP hPC hSPC hSCP hPs hCs hSs ) using 1;
  · rw [ inv_transpose_symm ];
    · rw [ ← inv_mul_comm ];
      · rw [ Matrix.add_mulVec ];
      · exact hPC;
      · exact hCP;
    · exact hSs.add hPs;
    · assumption;
  · rw [ ← inv_mul_comm ];
    · exact hSCP;
    · exact hSPC

/-
Coefficient-of-M.p identity for the p component associativity proof.
    From the identity (1+(S+P)*C) * (1+PC)⁻¹ = 1 + S*(1+CP)⁻¹*C:
    (1+(S+P)*C)⁻¹ + (1+(S+P)*C)⁻¹*S*(1+CP)⁻¹*C = (1+PC)⁻¹
-/
lemma p_mp_coeff
    (S P C : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ)
    (hCP : IsUnit (1 + C * P)) (hPC : IsUnit (1 + P * C))
    (hSPC : IsUnit (1 + C * (S + P))) (hSCP : IsUnit (1 + (S + P) * C)) :
    ((1 + (S + P) * C)⁻¹).mulVec v +
    ((1 + (S + P) * C)⁻¹ * S * (1 + C * P)⁻¹ * C).mulVec v =
    ((1 + P * C)⁻¹).mulVec v := by
  have h_push : (1 + C * P)⁻¹ * C = C * (1 + P * C)⁻¹ := by
    exact?;
  simp_all +decide [ mul_assoc, Matrix.mulVec_add, Matrix.mulVec_smul ];
  have h_rewrite : (1 + (S + P) * C) * (1 + P * C)⁻¹ = 1 + S * C * (1 + P * C)⁻¹ := by
    simp_all +decide [ add_mul, mul_assoc, Matrix.isUnit_iff_isUnit_det ];
    simp +decide [ ← mul_assoc, ← add_assoc, ← eq_sub_iff_add_eq', hPC ];
    rw [ show P * C = ( 1 + P * C ) - 1 by abel1, sub_mul, one_mul ];
    simp +decide [ hPC, isUnit_iff_ne_zero ];
  convert congr_arg ( fun x => ( 1 + ( S + P ) * C ) ⁻¹ *ᵥ x ) ( congr_arg ( fun x => x *ᵥ v ) h_rewrite.symm ) using 1 <;> simp +decide [ Matrix.mul_assoc, Matrix.mulVec_add, Matrix.mulVec_mulVec ];
  · simp +decide [ Matrix.mul_add, Matrix.add_mulVec, Matrix.mulVec_add ];
  · rw [ ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ ] ; aesop;
    exact IsUnit.map ( Matrix.detMonoidHom ) hSCP

theorem ivfCombine_assoc_p (L M R : IntervalValueFn n)
    (h : IVFAssocHyp L M R) :
    (ivfCombine (ivfCombine L M) R).p =
    (ivfCombine L (ivfCombine M R)).p := by
  obtain ⟨hL, hM, hR, hLM, hMR, hLMR⟩ := h;
  have h_pushthrough := pushthrough_resolvent_transpose M.Amat L.C M.P M.C R.P (by
  assumption) (by
  assumption) (by
  assumption) (by
  assumption) (by
  simp_all +decide [ Matrix.isUnit_iff_isUnit_det ];
  convert ‹¬ ( 1 + ( ivfCombine L M ).C * R.P ).det = 0› using 1) (by
  assumption) (by
  convert ‹IsUnit ( 1 + L.C * ( ivfCombine M R ).P ) › using 1) (by
  convert ‹IsUnit ( 1 + ( ivfCombine M R ).P * L.C ) › using 1);
  have h_p_cvec := p_cvec_coeff (M.Amatᵀ * (1 + R.P * M.C)⁻¹ * R.P * M.Amat) M.P L.C L.cvec (by
  assumption) (by
  assumption) (by
  assumption) (by
  convert ‹IsUnit ( 1 + ( ivfCombine M R ).P * L.C ) › using 1) (by
  assumption) (by
  assumption) (by
  apply_rules [ schur_symm ]);
  have h_p_mp := p_mp_coeff (M.Amatᵀ * (1 + R.P * M.C)⁻¹ * R.P * M.Amat) M.P L.C M.p (by
  assumption) (by
  assumption) (by
  assumption) (by
  convert ‹IsUnit ( 1 + ( ivfCombine M R ).P * L.C ) › using 1);
  unfold ivfCombine at *; simp_all +decide [ Matrix.mulVec_add, Matrix.mulVec_mulVec ] ;
  simp_all +decide [ ← Matrix.mulVec_mulVec, ← Matrix.mul_assoc, ← eq_sub_iff_add_eq' ];
  simp_all +decide [ Matrix.mulVec_sub, Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.transpose_nonsing_inv ];
  simp_all +decide [ ← Matrix.mulVec_mulVec, ← Matrix.mul_assoc, Matrix.IsSymm ];
  simp_all +decide [ Matrix.mulVec_sub, Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.transpose_nonsing_inv ];
  abel1

/-
Expansion identity for the cvec component:
    (1+QD)⁻¹(w + Qu) - w = ((1+QD)⁻¹Q)(u - Dw)
-/
lemma cvec_expansion (D Q : Matrix (Fin n) (Fin n) ℝ) (w u : Fin n → ℝ)
    (hQD : IsUnit (1 + Q * D)) :
    (1 + Q * D)⁻¹.mulVec (w + Q.mulVec u) - w =
    ((1 + Q * D)⁻¹ * Q).mulVec (u - D.mulVec w) := by
  simp_all +decide [ Matrix.isUnit_iff_isUnit_det ];
  have h_simp : (1 + Q * D)⁻¹ * (1 + Q * D) = 1 := by
    simp +decide [ hQD, isUnit_iff_ne_zero ];
  simp_all +decide [ mul_add, add_mul, mul_assoc, Matrix.mulVec_add, Matrix.mulVec_mulVec ];
  simp_all +decide [ mul_sub, ← eq_sub_iff_add_eq', ← Matrix.mul_assoc ];
  simp_all +decide [ mul_assoc, Matrix.mulVec_sub ];
  simp +decide [ sub_mul, Matrix.sub_mulVec ] ; abel_nf

/-
Coefficient identity for the cvec component:
    (1+C_total*Q)⁻¹ + (1+C_total*Q)⁻¹*(C_total-D)*(1+QD)⁻¹*Q = (1+DQ)⁻¹
    Analogous to p_mp_coeff but for the C/cvec structure.
-/
lemma cvec_coeff_identity
    (S D Q : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ)
    (hSDQ : IsUnit (1 + (S + D) * Q))
    (hDQ : IsUnit (1 + D * Q))
    (hQD : IsUnit (1 + Q * D)) :
    ((1 + (S + D) * Q)⁻¹).mulVec v +
    ((1 + (S + D) * Q)⁻¹ * S * (1 + Q * D)⁻¹ * Q).mulVec v =
    ((1 + D * Q)⁻¹).mulVec v := by
  convert p_mp_coeff S D Q v _ _ _ _ using 1;
  · bv_omega;
  · exact hDQ;
  · simp_all +decide [ Matrix.isUnit_iff_isUnit_det ];
    convert hSDQ using 1;
    rw [ ← Matrix.det_one_add_mul_comm ];
  · exact hSDQ

/-
The "pushthrough expansion" identity for cvec:
    (1+R.P*M.C)⁻¹.mulVec(R.p + R.P.mulVec M.cvec) - R.p = ((1+R.P*M.C)⁻¹*R.P).mulVec(M.cvec - M.C.mulVec R.p)
    Specialization of cvec_expansion.
-/
lemma cvec_pushthrough_expand (P₂ C₂ : Matrix (Fin n) (Fin n) ℝ)
    (p₂ c₂ : Fin n → ℝ) (hPC : IsUnit (1 + P₂ * C₂)) :
    (1 + P₂ * C₂)⁻¹.mulVec (p₂ + P₂.mulVec c₂) - p₂ =
    ((1 + P₂ * C₂)⁻¹ * P₂).mulVec (c₂ - C₂.mulVec p₂) := by
  convert cvec_expansion C₂ P₂ p₂ c₂ _ using 1;
  exact hPC

/-
Associativity of the c (offset) component.
-/
theorem ivfCombine_assoc_cvec (L M R : IntervalValueFn n)
    (h : IVFAssocHyp L M R) :
    (ivfCombine (ivfCombine L M) R).cvec =
    (ivfCombine L (ivfCombine M R)).cvec := by
  obtain ⟨hL, hM, hR, hLM, hMR, hLMR⟩ := h;
  have h_push := pushthrough_resolvent_mulVec M.Amat L.C M.P M.C R.P ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›;
  have h_expand := cvec_pushthrough_expand R.P M.C R.p M.cvec ‹_›
  have h_coeff := cvec_coeff_identity (M.Amat * (1+L.C*M.P)⁻¹ * L.C * M.Amatᵀ) M.C R.P (M.cvec - M.C.mulVec R.p) ‹_› ‹_› ‹_›;
  unfold ivfCombine at *; simp_all +decide [ Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mulVec_sub, Matrix.sub_mulVec, Matrix.mul_assoc ] ;
  simp_all +decide [ ← Matrix.mulVec_mulVec, ← Matrix.mulVec_add, ← Matrix.mulVec_sub, ← Matrix.mulVec_smul ];
  simp_all +decide [ Matrix.mulVec_add, Matrix.mulVec_sub, Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.add_mulVec, Matrix.sub_mulVec ];
  simp_all +decide [ ← Matrix.mulVec_mulVec, ← Matrix.mulVec_add, ← Matrix.mulVec_sub, ← Matrix.mulVec_smul, ← Matrix.mul_assoc, ← eq_sub_iff_add_eq ];
  simp_all +decide [ Matrix.mulVec_add, Matrix.mulVec_sub, Matrix.mulVec_mulVec, Matrix.mul_assoc, sub_eq_iff_eq_add' ];
  grobner

-- ═══════════════════════════════════════════════════════════════════════════
-- § 6. Main Associativity Theorem
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Associativity of ivfCombine**: the interval value function combination
    operator is associative (under symmetry of P and C), enabling
    parallelization via associative scans.

    This is the analogue of `affineCompose_assoc` (proved in `AffineAssoc.lean`)
    for the backward pass. Together, they establish that both the forward and
    backward passes of the LQR solve can be parallelized. -/
theorem ivfCombine_assoc (L M R : IntervalValueFn n)
    (h : IVFAssocHyp L M R) :
    ivfCombine (ivfCombine L M) R = ivfCombine L (ivfCombine M R) := by
  apply IntervalValueFn.ext'
  · exact ivfCombine_assoc_P L M R h
  · exact ivfCombine_assoc_p L M R h
  · exact ivfCombine_assoc_Amat L M R h
  · exact ivfCombine_assoc_C L M R h
  · exact ivfCombine_assoc_cvec L M R h