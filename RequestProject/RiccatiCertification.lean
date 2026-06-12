/-
# Riccati inertia certification

This file formalizes the *inertia-certification* result of
"Dual-Regularized Riccati Recursions for Interior-Point Optimal Control"
(Sousa-Pinto & Orban), `\label{riccati-inertia-certification-theorem}`.

The dual-regularized LQR first-order optimality matrix
`K_LQR = [[P, Cᵀ], [C, -Δ]]` (with `Δ ≻ 0`) has the descent-certifying inertia
`(N(n+m)+n, (N+1)n, 0)` **iff** every stage pivot of the sequential Riccati
recursion is positive definite.

The previous development already provides the two outer steps:

* `KKTInertia.kkt_inertia_iff` / `kkt_inertia_iff_lqr`: `K_LQR` has the correct
  inertia iff the reduced (Schur-complement) Hessian `M = P + Cᵀ Δ⁻¹ C ≻ 0`.
* `SmoothingPivot`: the state/co-state pivots are unconditionally definite.

The missing middle step is the *block `LDLᵀ` factorization*: the sequential
Riccati recursion expresses `M = Lᵀ · diag(pivots) · L` with `L` invertible.
We isolate this as an explicit hypothesis `hLDL` (the recursion's factorization)
and prove that, given it, `M ≻ 0` iff every pivot block is positive definite.
This is exactly the paper's argument: "By repeated application of Sylvester's law
of inertia, the inertia of `P + Cᵀ Δ⁻¹ C` is the sum of the inertias of the
`S_i` and `G_i` pivots."

## Reusable matrix infrastructure

* `posDef_congr_iff`: congruence by an invertible matrix preserves positive
  definiteness (over `ℝ`).
* `posDef_submatrix_equiv`: reindexing by an equivalence preserves positive
  definiteness.
* `blockDiagonal'_posDef_iff`: a block-diagonal matrix is positive definite iff
  every diagonal block is.
-/
import Mathlib
import RequestProject.KKTInertia

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

open Matrix
open scoped Matrix

namespace RiccatiCertification

open KKTInertia

/-- **Congruence invariance of positive definiteness.** For an invertible `U`
over `ℝ`, `Uᵀ * M * U` is positive definite iff `M` is. -/
theorem posDef_congr_iff {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) {U : Matrix ι ι ℝ} (hU : IsUnit U) :
    (Uᵀ * M * U).PosDef ↔ M.PosDef := by
  have := hU.posDef_star_left_conjugate_iff (x := M)
  simpa [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] using this

/-
**Reindexing invariance of positive definiteness.** Permuting the index set
by an equivalence preserves positive definiteness.
-/
theorem posDef_submatrix_equiv {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (e : κ ≃ ι) (M : Matrix ι ι ℝ) :
    (M.submatrix e e).PosDef ↔ M.PosDef := by
  constructor <;> intro h <;> constructor;
  · ext i j; have := congr_fun ( congr_fun h.1 ( e.symm i ) ) ( e.symm j ) ; aesop;
  · intro x hx; have := h.2; simp_all +decide [ Finsupp.sum_fintype] ;
    convert this ( show ( Finsupp.equivFunOnFinite.symm ( x ∘ e ) ) ≠ 0 from ?_ ) using 1;
    · simp +decide [ Finsupp.equivFunOnFinite];
      conv_lhs => rw [ ← Equiv.sum_comp e ] ;
      exact Finset.sum_congr rfl fun i _ => by rw [ ← Equiv.sum_comp e ] ;
    · simp_all +decide [ Finsupp.ext_iff];
      exact ⟨ e.symm hx.choose, by simpa using hx.choose_spec ⟩;
  · exact h.1.submatrix e;
  · intro x hx; have := h.2; simp_all +decide [ Finsupp.sum_fintype] ;
    convert this ( show ( x.sum fun i a => Finsupp.single ( e i ) a ) ≠ 0 from fun h => hx <| by ext i; simpa [ Finsupp.single_apply ] using congr_arg ( fun f => f ( e i ) ) h ) using 1;
    simp +decide [ Finsupp.sum_fintype, Finsupp.single_apply ];
    refine' Finset.sum_bij ( fun i _ => e i ) _ _ _ _ <;> simp +decide [ e.injective.eq_iff ];
    · exact e.surjective;
    · intro a; rw [ ← Equiv.sum_comp e ] ; simp +decide ;

/-
**Block-diagonal positive definiteness.** A block-diagonal matrix is
positive definite iff each of its diagonal blocks is.
-/
theorem blockDiagonal'_posDef_iff {J : Type*} [Fintype J] [DecidableEq J]
    {β : J → Type*} [∀ j, Fintype (β j)] [∀ j, DecidableEq (β j)]
    (Dp : (j : J) → Matrix (β j) (β j) ℝ) :
    (Matrix.blockDiagonal' Dp).PosDef ↔ ∀ j, (Dp j).PosDef := by
  constructor <;> intro h₂;
  · intro j;
    have := h₂.2;
    refine' ⟨ _, fun x hx => _ ⟩;
    · have := h₂.1;
      ext i k; replace this := congr_fun ( congr_fun this ( Sigma.mk j i ) ) ( Sigma.mk j k ) ; aesop;
    · convert this ( show Finsupp.equivFunOnFinite.symm ( fun p => if h : p.1 = j then x ( h ▸ p.2 ) else 0 ) ≠ 0 from ?_ ) using 1;
      · simp +decide [ Finsupp.sum_fintype, Finsupp.equivFunOnFinite ];
        rw [ ← Finset.sum_subset ( Finset.subset_univ ( Finset.image ( fun i => ⟨ j, i ⟩ : β j → ( i : J ) × β i ) Finset.univ ) ) ];
        · rw [ Finset.sum_image ] <;> simp +decide [ blockDiagonal' ];
          · refine' Finset.sum_congr rfl fun i hi => _;
            rw [ ← Finset.sum_subset ( Finset.subset_univ ( Finset.image ( fun i => ⟨ j, i ⟩ : β j → ( i : J ) × β i ) Finset.univ ) ) ];
            · rw [ Finset.sum_image ] <;> simp +decide;
              exact fun i j hij => by injection hij;
            · grind;
          · exact fun i j h => by injection h;
        · aesop;
      · simp_all +decide [ Finsupp.ext_iff ];
        exact ⟨ j, hx.choose, rfl, hx.choose_spec ⟩;
  · refine' ⟨ _, _ ⟩;
    · ext ⟨ j, i ⟩ ⟨ k, l ⟩ ; by_cases h : j = k <;> simp +decide;
      · subst h; simp +decide [ blockDiagonal' ] ;
        exact h₂ j |>.1.apply _ _ ▸ rfl;
      · simp +decide [ blockDiagonal', h ];
        grind;
    · intro x hx_ne_zero
      have h_sum_pos : 0 < ∑ j, ∑ i, ∑ k, x (Sigma.mk j i) * (Dp j) i k * x (Sigma.mk j k) := by
        -- Since $x \neq 0$, there exists some $j$ such that the restriction of $x$ to $\beta j$ is non-zero.
        obtain ⟨j, hj⟩ : ∃ j, ∃ y : β j → ℝ, y ≠ 0 ∧ ∑ i, ∑ k, y i * (Dp j) i k * y k > 0 ∧ ∀ i, x (Sigma.mk j i) = y i := by
          obtain ⟨j, hj⟩ : ∃ j, ∃ y : β j → ℝ, y ≠ 0 ∧ ∀ i, x (Sigma.mk j i) = y i := by
            obtain ⟨j, hj⟩ : ∃ j, ∃ i : β j, x (Sigma.mk j i) ≠ 0 := by
              contrapose! hx_ne_zero; aesop;
            exact ⟨ j, fun i => x ⟨ j, i ⟩, fun h => hj.elim fun i hi => hi <| by simpa using congr_fun h i, fun i => rfl ⟩;
          obtain ⟨ y, hy_ne_zero, hy ⟩ := hj; use j, y; simp_all +decide [ Matrix.PosDef ] ;
          convert h₂ j |>.2 ( show ( Finsupp.equivFunOnFinite.symm y ) ≠ 0 from by simpa [ Finsupp.ext_iff, funext_iff ] using hy_ne_zero ) using 1 ; simp +decide [ Finsupp.sum_fintype, Finsupp.equivFunOnFinite ];
        refine' lt_of_lt_of_le _ ( Finset.single_le_sum ( fun j _ => _ ) ( Finset.mem_univ j ) ) <;> simp_all +decide [ Matrix.PosDef ];
        · aesop;
        · by_cases h : ∃ y : β j → ℝ, y ≠ 0 ∧ ∑ i, ∑ k, y i * (Dp j) i k * y k > 0 ∧ ∀ i, x (Sigma.mk j i) = y i <;> simp_all +decide;
          · grind;
          · by_cases hx : x ∘ Sigma.mk j = 0 <;> simp_all +decide [ funext_iff ];
            contrapose! h;
            exact absurd h ( not_lt_of_ge ( by simpa [ Finsupp.sum_fintype ] using h₂ j |>.2 ( show ( Finsupp.equivFunOnFinite.symm ( fun i => x ⟨ j, i ⟩ ) ) ≠ 0 from by simpa [ Finsupp.ext_iff ] using hx ) |> le_of_lt ) );
      convert h_sum_pos using 1;
      simp +decide [ Finsupp.sum_fintype, blockDiagonal' ];
      rw [ Finset.sum_sigma' ];
      rw [ Finset.sum_sigma' ];
      rw [ Finset.sum_sigma' ];
      rw [ ← Finset.sum_subset ( show Finset.image ( fun p : ( j : J ) × β j × β j => ⟨ ⟨ p.1, p.2.1 ⟩, ⟨ p.1, p.2.2 ⟩ ⟩ ) ( Finset.univ : Finset ( ( j : J ) × β j × β j ) ) ⊆ Finset.univ.sigma fun j => Finset.univ from Finset.subset_univ _ ) ];
      · rw [ Finset.sum_image ];
        · refine' Finset.sum_bij ( fun p hp => ⟨ ⟨ p.1, p.2.1 ⟩, p.2.2 ⟩ ) _ _ _ _ <;> simp +decide;
          · grind;
          · exact fun b => ⟨ _, _, _, rfl ⟩;
        · intro p hp q hq h_eq; aesop;
      · simp +contextual [ Finset.mem_image ];
        grind

/-- **Riccati inertia certification** (`\label{riccati-inertia-certification-theorem}`).

Let `K_LQR = [[P, Cᵀ], [C, -Δ]]` be the first-order optimality matrix of a
dual-regularized LQR problem with `Δ ≻ 0`, and let `M = P + Cᵀ Δ⁻¹ C` be its
reduced (Schur-complement) Hessian.  Suppose the sequential Riccati recursion
provides a block-`LDLᵀ` factorization of `M`, i.e. there is an invertible `L` and
a family of pivot blocks `Dp` (the state pivots `S_i` and control pivots `G_i`)
with
`M = Lᵀ · blockDiagonal'(Dp) · L`
(read through the index equivalence `e`).

Then `K_LQR` has the descent-certifying inertia `(card ι, card κ, 0)` **iff**
every Riccati pivot `Dp j` is positive definite.

When specialized to the optimal-control dimensions `ι = Fin (N(n+m)+n)`,
`κ = Fin ((N+1)n)`, this is exactly the paper's statement: the inertia is correct
iff `S_i ≻ 0` for `i = 0,…,N` and `G_i ≻ 0` for `i = 0,…,N-1`. -/
theorem riccati_inertia_certification
    {ι κ J : Type*} [Fintype ι] [Fintype κ] [Fintype J]
    [DecidableEq ι] [DecidableEq κ] [DecidableEq J]
    {β : J → Type*} [∀ j, Fintype (β j)] [∀ j, DecidableEq (β j)]
    (P : Matrix ι ι ℝ) (C : Matrix κ ι ℝ) (Δ : Matrix κ κ ℝ)
    (hP : P.IsHermitian) (hΔ : Δ.PosDef)
    (Dp : (j : J) → Matrix (β j) (β j) ℝ)
    (e : ι ≃ Σ j, β j)
    (L : Matrix ι ι ℝ) (hL : IsUnit L)
    (hLDL : P + Cᵀ * Δ⁻¹ * C = Lᵀ * ((Matrix.blockDiagonal' Dp).submatrix e e) * L) :
    HasInertia (fromBlocks P Cᵀ C (-Δ)) (Fintype.card ι) (Fintype.card κ) 0
      ↔ ∀ j, (Dp j).PosDef := by
  rw [kkt_inertia_iff P C Δ hP hΔ, hLDL, posDef_congr_iff _ hL,
    posDef_submatrix_equiv e (Matrix.blockDiagonal' Dp), blockDiagonal'_posDef_iff]

end RiccatiCertification