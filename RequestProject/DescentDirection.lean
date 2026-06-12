/-
# Descent of the Augmented Barrier-Lagrangian merit function

This file formalizes the descent-direction results from
"Dual-Regularized Riccati Recursions for Interior-Point Optimal Control"
(Sousa-Pinto & Orban). Throughout, results are referenced by their LaTeX
`\label{...}` names in the paper source (`main.tex`), not by PDF-generated
numbers.

## Main result (`\label{inertia-al-descent-theorem}`)

`inertia_al_descent`: if the `4×4` Newton-KKT matrix `K₄`
(`\label{ipm-4x4-newton-kkt}`) has inertia `(n_x+n_g, n_c+n_g, 0)`, then the
primal component `(Δx, Δs)` of its solution either vanishes or is a strict
descent direction of the Augmented Barrier-Lagrangian merit function `𝒜`.

This is the new, *tighter* statement: it no longer requires the primal Hessian
`P` itself to be positive definite — only that the whole KKT matrix has the
correct inertia (which can be enforced by regularizing `P`).

## Supporting results

* `sylvester_inertia` (`\label{sylvester-inertia-lemma}`):
  `In([[H, Aᵀ],[A, -D]]) = In(-D) + In(H + Aᵀ D⁻¹ A)` for `D ≻ 0`.
  (Realized via `KKTInertia.kkt_posIndex` / `KKTInertia.kkt_negIndex`.)
  This is also exactly the inertia decomposition `\label{4x4-primal-inertia-lemma}`
  `In(K₄) = In(K_{xs}) + (0, n_c+n_g, 0)` when instantiated at the IPM blocks,
  with `K_{xs} = H + Aᵀ D⁻¹ A` the primal Schur complement.
* `primal_schur_posDef`: the positive-definiteness consequence of
  `\label{4x4-primal-inertia-lemma}` — correct inertia of `K₄` forces `K_{xs} ≻ 0`.
* `al_directional_derivative` (`\label{al-directional-derivative-lemma}`):
  `D(𝒜; (Δx, Δs)) = -[Δx;Δs]ᵀ K_{xs} [Δx;Δs]`.

The earlier, stronger-hypothesis statement (requiring `P, W⁻¹, Δ_C, Δ_G ≻ 0`
directly) is retained as `augmented_lagrangian_descent` for reference.

The variables Δx, Δs may live in different-dimensional spaces (Fin nx, Fin ns),
and the constraint Jacobians C, G are rectangular.
-/
import Mathlib
import RequestProject.KKTInertia

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

    This is the algebraic core of the strong-hypotheses descent statement
    `augmented_lagrangian_descent` below. The fully general, tighter result is
    `inertia_al_descent` (`\label{inertia-al-descent-theorem}`). -/
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
-- § 2. Descent under explicit positive-definiteness hypotheses
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
**Descent direction under explicit positive-definiteness hypotheses.**

This is the stronger-hypotheses statement: it assumes `P, W⁻¹, Δ_C, Δ_G ≻ 0`
directly. The tighter result requiring only correct inertia of `K₄` is
`inertia_al_descent` (`\label{inertia-al-descent-theorem}`).

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
      simp +decide [ Matrix.add_vecMul, Matrix.mul_assoc, Matrix.vecMul_mulVec ] ; ring;
    convert h_neg using 1;
    rw [ ← eq_sub_iff_add_eq' ] at * ; simp_all +decide [ Matrix.mulVec_add, dotProduct_add ] ; ring;
    simp +decide [ dotProduct_comm ];
  · simp_all +decide [ dotProduct ];
    -- By definition of $h$, we know that $ds \neq 0$.
    have h_ds : 0 < dotProduct ds (Winv.mulVec ds) + dotProduct ds (DeltaG.mulVec ds) := by
      exact add_pos_of_nonneg_of_pos ( posDef_dotProduct_nonneg' hW ds ) ( posDef_dotProduct_pos' hDG h );
    simp_all +decide [ ← eq_sub_iff_add_eq' ];
    simpa only [ dotProduct, mul_comm ] using h_ds
-- ═══════════════════════════════════════════════════════════════════════════
-- § 3. Inertia-based descent theorem (the tighter statement)
-- ═══════════════════════════════════════════════════════════════════════════

/-! This section formalizes the new, tighter descent guarantee. Following the
paper, we write the Newton-KKT matrix in the symmetric saddle form

  `K₄ = [[H, Aᵀ], [A, -D]]`,

with `H = [[P, 0], [0, W⁻¹]]` the primal Hessian, `A = [[C, 0], [G, I]]` the
constraint Jacobian, and `D = [[Δ_C⁻¹, 0], [0, Δ_G⁻¹]]` the (positive-definite)
dual regularization. The primal Schur complement is `K_{xs} = H + Aᵀ D⁻¹ A`.

We work at the level of abstract index types `ι` (primal) and `κ` (dual); the
concrete IPM block instantiation is `ι = Fin nx ⊕ Fin ns`, `κ = Fin nc ⊕ Fin ns`,
for which `Fintype.card ι = n_x + n_g` and `Fintype.card κ = n_c + n_g`. -/

open KKTInertia

section AbstractDescent

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-
**Sylvester inertia lemma** (`\label{sylvester-inertia-lemma}`).

For symmetric `H`, arbitrary `A`, and positive-definite `D`, the saddle matrix
`[[H, Aᵀ], [A, -D]]` has inertia `In(-D) + In(H + Aᵀ D⁻¹ A)`. Since `D ≻ 0`,
`In(-D) = (0, card κ, 0)`, so if the primal Schur complement `H + Aᵀ D⁻¹ A` has
inertia `(p, q, z)`, then the saddle matrix has inertia `(p, q + card κ, z)`.
-/
theorem sylvester_inertia
    (H : Matrix ι ι ℝ) (A : Matrix κ ι ℝ) (D : Matrix κ κ ℝ) (hD : D.PosDef)
    {p q z : ℕ}
    (hSchur : HasInertia (H + Aᵀ * D⁻¹ * A) p q z) :
    HasInertia (fromBlocks H Aᵀ A (-D)) p (q + Fintype.card κ) z := by
  have h_card : Fintype.card ι = p + q + z := by
    exact hSchur.2.2;
  refine' ⟨ kkt_posIndex H A D hD |> fun h => h.trans hSchur.1, kkt_negIndex H A D hD |> fun h => h.trans ( by rw [ hSchur.2.1 ] ), _ ⟩;
  simp +arith +decide [ h_card ]

/-
**Primal Schur inertia** (`\label{4x4-primal-inertia-lemma}`).

If the saddle matrix `[[H, Aᵀ], [A, -D]]` (i.e. `K₄`) has the full positive
inertia `(card ι, card κ, 0)`, then the primal Schur complement
`K_{xs} = H + Aᵀ D⁻¹ A` is positive definite.
-/
theorem primal_schur_posDef
    (H : Matrix ι ι ℝ) (A : Matrix κ ι ℝ) (D : Matrix κ κ ℝ)
    (hH : H.IsHermitian) (hD : D.PosDef)
    (hin : HasInertia (fromBlocks H Aᵀ A (-D)) (Fintype.card ι) (Fintype.card κ) 0) :
    (H + Aᵀ * D⁻¹ * A).PosDef := by
  convert KKTInertia.kkt_inertia_iff H A D hH hD |>.1 ?_;
  exact hin

/-
**Directional-derivative identity** (`\label{al-directional-derivative-lemma}`).

Let `(w_p, w_d)` solve the shifted KKT system

  `H w_p + Aᵀ w_d = -grad_p`,   `A w_p - D w_d = 0`

(the second is the dual block of the shifted system in
`\label{shifted-kkt-al-gradient-lemma}`). Then the directional derivative of the
merit function along the primal direction `w_p`, namely `grad_p ⬝ w_p`, equals
`-(w_p ⬝ K_{xs} w_p)` where `K_{xs} = H + Aᵀ D⁻¹ A`.
-/
theorem al_directional_derivative
    (H : Matrix ι ι ℝ) (A : Matrix κ ι ℝ) (D : Matrix κ κ ℝ) (hD : IsUnit D)
    (w_p : ι → ℝ) (w_d : κ → ℝ) (grad_p : ι → ℝ)
    (hprimal : H *ᵥ w_p + Aᵀ *ᵥ w_d = -grad_p)
    (hdual : A *ᵥ w_p - D *ᵥ w_d = 0) :
    grad_p ⬝ᵥ w_p = - (w_p ⬝ᵥ (H + Aᵀ * D⁻¹ * A) *ᵥ w_p) := by
  simp_all +decide [ sub_eq_zero ];
  convert congr_arg ( fun x => - ( w_p ⬝ᵥ x ) ) hprimal using 1;
  · simp +decide [ hprimal, dotProduct_comm ];
  · simp +decide [ ← hprimal, Matrix.add_mulVec];
    simp +decide [ ← Matrix.mulVec_mulVec, hdual ];
    cases hD.nonempty_invertible ; aesop

/-
**Inertia descent theorem** (`\label{inertia-al-descent-theorem}`).

If the Newton-KKT matrix `K₄ = [[H, Aᵀ], [A, -D]]` has inertia
`(card ι, card κ, 0)` (i.e. `(n_x+n_g, n_c+n_g, 0)`), then the primal component
`w_p` of any solution `(w_p, w_d)` of the shifted KKT system gives a strict
descent direction unless `w_p = 0`: the directional derivative `grad_p ⬝ w_p` is
strictly negative whenever `w_p ≠ 0`.
-/
theorem inertia_al_descent
    (H : Matrix ι ι ℝ) (A : Matrix κ ι ℝ) (D : Matrix κ κ ℝ)
    (hH : H.IsHermitian) (hD : D.PosDef)
    (hin : HasInertia (fromBlocks H Aᵀ A (-D)) (Fintype.card ι) (Fintype.card κ) 0)
    (w_p : ι → ℝ) (w_d : κ → ℝ) (grad_p : ι → ℝ)
    (hprimal : H *ᵥ w_p + Aᵀ *ᵥ w_d = -grad_p)
    (hdual : A *ᵥ w_p - D *ᵥ w_d = 0)
    (hne : w_p ≠ 0) :
    grad_p ⬝ᵥ w_p < 0 := by
  have := @KKTInertia.kkt_inertia_iff;
  specialize this H A D hH hD;
  obtain ⟨h_pos, h_neg⟩ := this.mp hin;
  convert neg_neg_of_pos ( h_neg ( show ( Finsupp.equivFunOnFinite.symm w_p ) ≠ 0 from by simpa [ Finsupp.ext_iff, funext_iff ] using hne ) ) using 1;
  convert al_directional_derivative H A D hD.isUnit w_p w_d grad_p hprimal hdual using 1;
  simp +decide [ Finsupp.sum_fintype, dotProduct, Matrix.mulVec, Finset.mul_sum _ _ _];
  simp +decide only [mul_assoc]

end AbstractDescent
-- ═══════════════════════════════════════════════════════════════════════════
-- § 4. Concrete IPM-block instantiation of the inertia descent theorem
-- ═══════════════════════════════════════════════════════════════════════════

/-! Here we instantiate `inertia_al_descent` at the concrete `4×4` Newton-KKT
matrix `K₄` (`\label{ipm-4x4-newton-kkt}`), assembling its blocks from the
primal Hessian `P`, the smoothing block `W⁻¹`, the constraint Jacobians `C, G`
and the dual regularizations `Δ_C, Δ_G`. The primal variables are
`ι = Fin nx ⊕ Fin ns` and the dual variables `κ = Fin nc ⊕ Fin ns`, so that
`card ι = n_x + n_g` and `card κ = n_c + n_g`. -/

open KKTInertia

section IPMConcrete

variable {nx ns nc : ℕ} [DecidableEq (Fin nx)] [DecidableEq (Fin ns)] [DecidableEq (Fin nc)]

/-
A block-diagonal matrix of two positive-definite blocks is positive
definite.
-/
theorem fromBlocks_posDef_diag {a b : ℕ}
    (X : Matrix (Fin a) (Fin a) ℝ) (Y : Matrix (Fin b) (Fin b) ℝ)
    (hX : X.PosDef) (hY : Y.PosDef) :
    (fromBlocks X 0 0 Y).PosDef := by
  constructor;
  · simp_all +decide [ Matrix.IsHermitian, Matrix.fromBlocks_transpose ];
    exact ⟨ hX.1, hY.1 ⟩;
  · intro x hx; simp_all +decide [ Finsupp.sum_fintype] ;
    by_cases h : ∃ i, x ( Sum.inl i ) ≠ 0 <;> simp_all +decide [ Matrix.PosDef ];
    · refine' add_pos_of_pos_of_nonneg _ _;
      · convert hX.2 ( show ( Finsupp.equivFunOnFinite.symm ( fun i => x ( Sum.inl i ) ) ) ≠ 0 from fun h' => h.elim fun i hi => hi <| by simpa using congr_arg ( fun f => f i ) h' ) using 1;
        simp +decide [ Finsupp.sum_fintype, Finsupp.equivFunOnFinite ];
      · by_cases h : ∃ i, x (Sum.inr i) ≠ 0 <;> simp_all +decide [ Finsupp.sum_fintype ];
        exact le_of_lt ( hY.2 ( show ( Finsupp.equivFunOnFinite.symm ( fun i => x ( Sum.inr i ) ) ) ≠ 0 from by simpa [ Finsupp.ext_iff, funext_iff ] using h ) );
    · convert hY.2 ( show ( Finsupp.equivFunOnFinite.symm ( fun i => x ( Sum.inr i ) ) ) ≠ 0 from ?_ ) using 1;
      · simp +decide [ Finsupp.sum_fintype, Finsupp.equivFunOnFinite ];
      · contrapose! hx; ext i; cases i <;> simp_all +decide [ Finsupp.ext_iff ] ;

/-
**Inertia descent theorem, concrete IPM form** (`\label{inertia-al-descent-theorem}`).

Let `K₄ = [[P, 0, Cᵀ, Gᵀ], [0, W⁻¹, 0, I], [C, 0, -Δ_C⁻¹, 0], [G, I, 0, -Δ_G⁻¹]]`
be the regularized interior-point Newton-KKT matrix (`\label{ipm-4x4-newton-kkt}`),
written here in permuted saddle form `[[H, Aᵀ], [A, -D]]` with
`H = [[P,0],[0,W⁻¹]]`, `A = [[C,0],[G,I]]`, `D = [[Δ_C⁻¹,0],[0,Δ_G⁻¹]]`.

If `K₄` has inertia `(n_x+n_g, n_c+n_g, 0)`, and `(Δx, Δs)` together with the
shifted multipliers `(Δỹ, Δz̃)` solve the shifted Newton system
(`\label{shifted-kkt-al-gradient-lemma}`), then the directional derivative of the
Augmented Barrier-Lagrangian merit function along `(Δx, Δs)`, namely
`grad_x ⬝ Δx + grad_s ⬝ Δs`, is strictly negative whenever `(Δx, Δs) ≠ 0`.
-/
theorem ipm_inertia_descent
    (P : Matrix (Fin nx) (Fin nx) ℝ)
    (Winv : Matrix (Fin ns) (Fin ns) ℝ)
    (C : Matrix (Fin nc) (Fin nx) ℝ)
    (G : Matrix (Fin ns) (Fin nx) ℝ)
    (DeltaCinv : Matrix (Fin nc) (Fin nc) ℝ)
    (DeltaGinv : Matrix (Fin ns) (Fin ns) ℝ)
    (hP : P.IsHermitian) (hW : Winv.IsHermitian)
    (hDC : DeltaCinv.PosDef) (hDG : DeltaGinv.PosDef)
    (hin : HasInertia
      (fromBlocks (fromBlocks P 0 0 Winv) (fromBlocks C 0 G 1)ᵀ
        (fromBlocks C 0 G 1) (-(fromBlocks DeltaCinv 0 0 DeltaGinv)))
      (nx + ns) (nc + ns) 0)
    (dx : Fin nx → ℝ) (ds : Fin ns → ℝ)
    (grad_x : Fin nx → ℝ) (grad_s : Fin ns → ℝ)
    (dy_tilde : Fin nc → ℝ) (dz_tilde : Fin ns → ℝ)
    -- shifted KKT row 1 (x):  P Δx + Cᵀ Δỹ + Gᵀ Δz̃ = -grad_x
    (hr1 : P *ᵥ dx + Cᵀ *ᵥ dy_tilde + Gᵀ *ᵥ dz_tilde = -grad_x)
    -- shifted KKT row 2 (s):  W⁻¹ Δs + Δz̃ = -grad_s
    (hr2 : Winv *ᵥ ds + dz_tilde = -grad_s)
    -- shifted KKT row 3 (y):  C Δx - Δ_C⁻¹ Δỹ = 0
    (hr3 : C *ᵥ dx - DeltaCinv *ᵥ dy_tilde = 0)
    -- shifted KKT row 4 (z):  G Δx + Δs - Δ_G⁻¹ Δz̃ = 0
    (hr4 : G *ᵥ dx + ds - DeltaGinv *ᵥ dz_tilde = 0)
    (hne : dx ≠ 0 ∨ ds ≠ 0) :
    grad_x ⬝ᵥ dx + grad_s ⬝ᵥ ds < 0 := by
  -- Let's define the augmented vectors and matrices.
  set H : Matrix (Fin nx ⊕ Fin ns) (Fin nx ⊕ Fin ns) ℝ := fromBlocks P 0 0 Winv
  set A : Matrix (Fin nc ⊕ Fin ns) (Fin nx ⊕ Fin ns) ℝ := fromBlocks C 0 G 1
  set D : Matrix (Fin nc ⊕ Fin ns) (Fin nc ⊕ Fin ns) ℝ := fromBlocks DeltaCinv 0 0 DeltaGinv;
  have h_primal : H.mulVec (Sum.elim dx ds) + Aᵀ.mulVec (Sum.elim dy_tilde dz_tilde) = -Sum.elim grad_x grad_s := by
    simp +zetaDelta at *;
    ext i; rcases i with ( i | i ) <;> simp +decide [ *, Matrix.mulVec ] ;
    · convert congr_fun hr1 i using 1 ; simp +decide [ Matrix.mulVec, dotProduct ] ; ring!;
    · convert congr_fun hr2 i using 1 ; simp +decide [ Matrix.mulVec, dotProduct ];
      simp +decide [ Matrix.one_apply ];
  have h_dual : A.mulVec (Sum.elim dx ds) - D.mulVec (Sum.elim dy_tilde dz_tilde) = 0 := by
    simp +zetaDelta at *;
    ext i; rcases i with ( i | i ) <;> simp_all +decide [ Matrix.mulVec, dotProduct ] ;
    · simpa [ Matrix.mulVec, dotProduct ] using congr_fun hr3 i;
    · simp_all +decide [ funext_iff, Matrix.one_apply ];
      simpa [ Matrix.mulVec, dotProduct ] using hr4 i;
  have := inertia_al_descent H A D ?_ ?_ ?_ ( Sum.elim dx ds ) ( Sum.elim dy_tilde dz_tilde ) ( Sum.elim grad_x grad_s ) h_primal h_dual ?_;
  · convert this using 1;
    simp +decide [ dotProduct];
  · simp +zetaDelta at *;
    simp_all +decide [ Matrix.IsHermitian, Matrix.fromBlocks_transpose ];
  · convert fromBlocks_posDef_diag DeltaCinv DeltaGinv hDC hDG using 1;
  · simpa using hin;
  · contrapose! hne; simp_all +decide [ funext_iff] ;

end IPMConcrete