/-
# Inertia of the First-Order (KKT) System of a Dual-Regularized LQR Problem

This file characterises *when* the symmetric "first-order condition" (KKT) matrix

```
  K = [ P    Cᵀ ]
      [ C   -Δ  ]
```

of a dual-regularized LQR problem has the inertia `(N(n+m)+n, (N+1)n, 0)` — i.e.
exactly `N(n+m)+n` positive directions (one per primal variable, the states and
controls), exactly `(N+1)n` negative directions (one per dual/co-state variable),
and **no** zero directions.

The answer (`kkt_inertia_iff`) is:

> With the dual regularization `Δ` symmetric positive definite, `K` has the desired
> inertia **iff** the *dual-regularized reduced (Schur-complement) Hessian*
> `P + Cᵀ Δ⁻¹ C` is positive definite.

The reduced Hessian `P + Cᵀ Δ⁻¹ C` is precisely the matrix that the sequential
dual-regularized Riccati backward pass (see `SequentialRiccati.lean` /
`DualRegLQR.lean`) factorizes stage by stage.  Hence the condition can be phrased
in factorization terms: the recursion runs to completion with every stage pivot
`Gₖ = Rₖ + Bₖᵀ Wₖ₊₁ Bₖ` (and the final state pivot) **positive definite**.

## Inertia, formally

We use the classical, coordinate-free notion of the inertia indices of a real
symmetric matrix:

* `posIndex M` — the maximal dimension of a subspace on which the quadratic form
  `x ↦ xᵀ M x` is positive definite (the number of positive eigenvalues);
* `negIndex M = posIndex (-M)` — likewise for negative directions.

These are manifestly invariant under congruence `M ↦ Uᵀ M U` with `U` invertible
(`posIndex_congr`), which is the key tool: the congruence
`Lᵀ K L = diag(P + Cᵀ Δ⁻¹ C, -Δ)` (block elimination of the dual block) reduces
the inertia of `K` to that of the reduced Hessian.
-/
import Mathlib

open Matrix
open scoped Matrix

set_option maxHeartbeats 1000000

namespace KKTInertia

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- A subspace `V ⊆ (ι → ℝ)` is *positive* for the matrix `M` if the quadratic
form `x ↦ xᵀ M x` is strictly positive on every nonzero element of `V`. -/
def IsPosSubspace (M : Matrix ι ι ℝ) (V : Submodule ℝ (ι → ℝ)) : Prop :=
  ∀ x ∈ V, x ≠ 0 → 0 < x ⬝ᵥ M *ᵥ x

/-- The set of dimensions attained by positive subspaces of `M`. -/
def posDims (M : Matrix ι ι ℝ) : Set ℕ :=
  {k | ∃ V : Submodule ℝ (ι → ℝ), Module.finrank ℝ V = k ∧ IsPosSubspace M V}

/-- The positive inertia index of `M`: the maximal dimension of a positive
subspace (equivalently, the number of positive eigenvalues). -/
noncomputable def posIndex (M : Matrix ι ι ℝ) : ℕ := sSup (posDims M)

/-- The negative inertia index of `M`. -/
noncomputable def negIndex (M : Matrix ι ι ℝ) : ℕ := posIndex (-M)

/-- `M` has inertia `(p, q, z)`: `p` positive directions, `q` negative directions,
and `z` zero directions (so that `p + q + z` is the dimension). -/
def HasInertia (M : Matrix ι ι ℝ) (p q z : ℕ) : Prop :=
  posIndex M = p ∧ negIndex M = q ∧ Fintype.card ι = p + q + z

/-
═══════════════════════════════════════════════════════════════════════════
§ 1. Basic facts about `posIndex`
═══════════════════════════════════════════════════════════════════════════
-/
theorem posDims_subset_Iic (M : Matrix ι ι ℝ) :
    posDims M ⊆ Set.Iic (Fintype.card ι) := by
  intro k;
  rintro ⟨ V, hV₁, hV₂ ⟩;
  exact hV₁ ▸ le_trans ( Submodule.finrank_le _ ) ( by simp +decide )

theorem posDims_bddAbove (M : Matrix ι ι ℝ) : BddAbove (posDims M) := by
  refine' ⟨ Fintype.card ι, fun k hk => _ ⟩;
  exact posDims_subset_Iic M hk

theorem posDims_zero_mem (M : Matrix ι ι ℝ) : 0 ∈ posDims M := by
  refine' ⟨ ⊥, _, _ ⟩ <;> norm_num;
  intro x hx hx'; aesop;

theorem posDims_nonempty (M : Matrix ι ι ℝ) : (posDims M).Nonempty :=
  ⟨0, posDims_zero_mem M⟩

/-
If `V` is a positive subspace of `M`, its dimension is `≤ posIndex M`.
-/
theorem finrank_le_posIndex {M : Matrix ι ι ℝ} {V : Submodule ℝ (ι → ℝ)}
    (hV : IsPosSubspace M V) : Module.finrank ℝ V ≤ posIndex M := by
  exact_mod_cast le_csSup ( posDims_bddAbove M ) ⟨ V, rfl, hV ⟩

/-
`posIndex` is attained by some positive subspace.
-/
theorem exists_posIndex (M : Matrix ι ι ℝ) :
    ∃ V : Submodule ℝ (ι → ℝ), Module.finrank ℝ V = posIndex M ∧ IsPosSubspace M V := by
  convert Nat.sSup_mem ( posDims_nonempty M ) ( posDims_bddAbove M )

theorem posIndex_le_card (M : Matrix ι ι ℝ) : posIndex M ≤ Fintype.card ι := by
  convert csSup_le ( posDims_nonempty M ) fun k hk => ?_;
  exact posDims_subset_Iic M hk

/-
═══════════════════════════════════════════════════════════════════════════
§ 2. `posIndex` versus positive / negative definiteness
═══════════════════════════════════════════════════════════════════════════

If the whole space is a positive subspace (i.e. `M` is positive definite),
then `posIndex M` is full.
-/
theorem posIndex_eq_card_of_posDef {M : Matrix ι ι ℝ} (hM : M.PosDef) :
    posIndex M = Fintype.card ι := by
  refine' le_antisymm _ _;
  · exact posIndex_le_card M;
  · refine' le_csSup ( posDims_bddAbove M ) _;
    refine' ⟨ ⊤, _, _ ⟩ <;> simp_all +decide [ Matrix.PosDef ];
    intro x hx; by_cases hx0 : x = 0 <;> simp_all +decide [ Finsupp.sum_fintype, dotProduct ] ;
    simpa [ Matrix.mulVec, dotProduct, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _ ] using hM.2 ( show ( Finsupp.equivFunOnFinite.symm x ) ≠ 0 from by simpa [ Finsupp.ext_iff, funext_iff ] using hx0 )

/-
Conversely, a full positive index forces positive definiteness (for a
symmetric matrix).
-/
theorem posDef_of_posIndex_eq_card {M : Matrix ι ι ℝ} (hsymm : M.IsHermitian)
    (h : posIndex M = Fintype.card ι) : M.PosDef := by
  -- By `exists_posIndex M` get `V` with `Module.finrank ℝ V = posIndex M = Fintype.card ι` and `IsPosSubspace M V`.
  obtain ⟨V, hV⟩ : ∃ V : Submodule ℝ (ι → ℝ), Module.finrank ℝ V = posIndex M ∧ IsPosSubspace M V := exists_posIndex M;
  -- Since `Module.finrank ℝ V = Fintype.card ι = Module.finrank ℝ (ι → ℝ)` (using `Module.finrank_pi`/`Module.finrank_fintype_fun_eq_card`), `V = ⊤` by `Submodule.eq_top_of_finrank_eq`.
  have hV_top : V = ⊤ := by
    exact Submodule.eq_top_of_finrank_eq ( by aesop );
  refine' ⟨ hsymm, _ ⟩;
  intro x hx_ne; specialize hV; have := hV.2 ( x ) ; simp_all +decide [ Matrix.mulVec, dotProduct ] ;
  simp_all +decide [ Finsupp.sum_fintype, mul_comm, mul_left_comm, Finset.mul_sum _ _ _ ]

/-- A symmetric matrix is positive definite iff its positive index is full. -/
theorem posDef_iff_posIndex_eq_card {M : Matrix ι ι ℝ} (hsymm : M.IsHermitian) :
    M.PosDef ↔ posIndex M = Fintype.card ι :=
  ⟨posIndex_eq_card_of_posDef, posDef_of_posIndex_eq_card hsymm⟩

/-
If the form of `M` is negative on every nonzero vector, there is no nonzero
positive subspace, so `posIndex M = 0`.
-/
theorem posIndex_eq_zero_of_neg {M : Matrix ι ι ℝ}
    (hM : ∀ x : ι → ℝ, x ≠ 0 → x ⬝ᵥ M *ᵥ x < 0) : posIndex M = 0 := by
  refine' le_antisymm ( csSup_le _ _ ) ( Nat.zero_le _ );
  · exact ⟨ 0, posDims_zero_mem M ⟩;
  · rintro k ⟨ V, rfl, hV ⟩;
    contrapose! hM;
    obtain ⟨ x, hx ⟩ := ( show ∃ x : ι → ℝ, x ∈ V ∧ x ≠ 0 from by simpa [ Submodule.eq_bot_iff ] using hM.ne' ) ; exact ⟨ x, hx.2, le_of_lt ( hV x hx.1 hx.2 ) ⟩ ;

/-
═══════════════════════════════════════════════════════════════════════════
§ 3. Congruence invariance
═══════════════════════════════════════════════════════════════════════════

**Congruence invariance.** For an invertible `U`, `posIndex (Uᵀ M U) = posIndex M`.
-/
theorem posIndex_congr [DecidableEq ι] (M : Matrix ι ι ℝ) {U : Matrix ι ι ℝ}
    (hU : IsUnit U) : posIndex (Uᵀ * M * U) = posIndex M := by
  refine' le_antisymm _ _;
  · obtain ⟨V, hV_dim, hV_pos⟩ : ∃ V : Submodule ℝ (ι → ℝ), Module.finrank ℝ V = posIndex (Uᵀ * M * U) ∧ IsPosSubspace (Uᵀ * M * U) V := exists_posIndex (Uᵀ * M * U);
    -- Let `e : (ι → ℝ) ≃ₗ[ℝ] (ι → ℝ)` be the linear equivalence `x ↦ U *ᵥ x`.
    obtain ⟨e, he⟩ : ∃ e : (ι → ℝ) ≃ₗ[ℝ] (ι → ℝ), ∀ x : ι → ℝ, e x = U *ᵥ x := by
      refine' ⟨ _, _ ⟩;
      refine' ( LinearEquiv.ofBijective ( Matrix.mulVecLin U ) _ );
      all_goals simp_all +decide [ Matrix.isUnit_iff_isUnit_det ];
      exact ⟨ fun x y hxy => by simpa [ hU, isUnit_iff_ne_zero ] using congr_arg ( fun z => U⁻¹.mulVec z ) hxy, fun x => ⟨ U⁻¹.mulVec x, by simp +decide [ hU, isUnit_iff_ne_zero ] ⟩ ⟩;
    -- Let `W := V.map e`. For `w ∈ W`, `w = U *ᵥ v` with `v ∈ V`; the quadratic-form identity gives `w ⬝ᵥ M *ᵥ w = (U *ᵥ v) ⬝ᵥ M *ᵥ (U *ᵥ v) = v ⬝ᵥ N *ᵥ v` (since `N = UᵀMU` and `(U *ᵥ v) ⬝ᵥ M *ᵥ (U *ᵥ v) = v ⬝ᵥ (Uᵀ M U) *ᵥ v`).
    have hW_pos : IsPosSubspace M (V.map e.toLinearMap) := by
      intro w hw hw'; obtain ⟨ v, hv, rfl ⟩ := hw; simp_all +decide [ Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec ] ;
      convert hV_pos v hv ( by aesop ) using 1;
      simp +decide [ Matrix.mul_assoc, Matrix.dotProduct_mulVec, Matrix.vecMul_mulVec ];
    have := finrank_le_posIndex hW_pos; simp_all +decide ;
    rw [ ← hV_dim, LinearEquiv.finrank_map_eq ] at * ; aesop;
  · obtain ⟨V, hV⟩ : ∃ V : Submodule ℝ (ι → ℝ), Module.finrank ℝ V = posIndex M ∧ IsPosSubspace M V := exists_posIndex M;
    -- Let $W := V.map (Matrix.mulVecLin U⁻¹)$. Then $W$ is a positive subspace for $N := Uᵀ * M * U$.
    set W : Submodule ℝ (ι → ℝ) := Submodule.map (LinearMap.pi fun i => ∑ j, (U⁻¹) i j • LinearMap.proj j) V
    have hW : IsPosSubspace (Uᵀ * M * U) W := by
      intro x hx hx_ne_zero
      obtain ⟨v, hvV, hvx⟩ : ∃ v ∈ V, x = Matrix.mulVec U⁻¹ v := by
        aesop;
      have h_quad_form : x ⬝ᵥ (Uᵀ * M * U) *ᵥ x = v ⬝ᵥ M *ᵥ v := by
        cases hU.nonempty_invertible ; simp_all +decide [ Matrix.mul_assoc, Matrix.dotProduct_mulVec, Matrix.vecMul_mulVec ];
        simp +decide [ ← Matrix.mul_assoc, Matrix.transpose_nonsing_inv ];
      exact h_quad_form.symm ▸ hV.2 v hvV ( by aesop );
    have hW_finrank : Module.finrank ℝ W = Module.finrank ℝ V := by
      have hW_finrank : Function.Injective (Matrix.mulVecLin U⁻¹) := by
        intro x y hxy; replace hxy := congr_arg ( fun z => U.mulVec z ) hxy; simp_all +decide [ Matrix.isUnit_iff_isUnit_det ] ;
      have hW_finrank : LinearMap.range (LinearMap.restrictScalars ℝ (Matrix.mulVecLin U⁻¹) ∘ₗ Submodule.subtype V) = W := by
        ext; simp [W];
        simp +decide [ funext_iff, Matrix.mulVec, dotProduct ];
      rw [ ← hW_finrank, LinearMap.finrank_range_of_inj ];
      exact ‹Function.Injective ( Matrix.mulVecLin U⁻¹ ) ›.comp Subtype.val_injective;
    exact hV.1 ▸ hW_finrank ▸ finrank_le_posIndex hW

/-
═══════════════════════════════════════════════════════════════════════════
§ 4. Block-diagonal building blocks
═══════════════════════════════════════════════════════════════════════════

The quadratic form of a block-diagonal matrix splits as a sum.
-/
theorem fromBlocks_diag_quadForm (M : Matrix ι ι ℝ) (D : Matrix κ κ ℝ)
    (x : ι → ℝ) (y : κ → ℝ) :
    (Sum.elim x y) ⬝ᵥ (fromBlocks M 0 0 D) *ᵥ (Sum.elim x y)
      = x ⬝ᵥ M *ᵥ x + y ⬝ᵥ D *ᵥ y := by
  simp +decide [ Matrix.mulVec, dotProduct ]

/-
A positive subspace of the top-left block embeds into the block-diagonal
matrix, so `posIndex M ≤ posIndex (diag M D)`.
-/
theorem posIndex_le_fromBlocks_left (M : Matrix ι ι ℝ) (D : Matrix κ κ ℝ) :
    posIndex M ≤ posIndex (fromBlocks M 0 0 D) := by
  obtain ⟨ V, hV₁, hV₂ ⟩ := exists_posIndex M;
  refine' le_trans _ ( finrank_le_posIndex _ );
  rotate_left;
  exact Submodule.map ( show ( ι → ℝ ) →ₗ[ℝ] ( ι ⊕ κ → ℝ ) from { toFun := fun x => Sum.elim x 0, map_add' := fun x y => by ext i; cases i <;> simp +decide, map_smul' := fun c x => by ext i; cases i <;> simp +decide } ) V;
  · intro x hx; obtain ⟨ y, hy, rfl ⟩ := hx; simp_all +decide [ IsPosSubspace ] ;
    intro h; specialize hV₂ y hy; simp_all +decide [ Matrix.mulVec, dotProduct ] ;
    exact hV₂ ( by contrapose! h; aesop );
  · convert hV₁.ge using 1;
    apply_rules [ LinearEquiv.finrank_eq ];
    symm;
    refine' ( LinearEquiv.ofBijective _ ⟨ _, _ ⟩ );
    refine' { toFun := fun x => ⟨ _, Submodule.mem_map_of_mem x.2 ⟩, map_add' := _, map_smul' := _ };
    all_goals simp +decide [ Function.Injective, Function.Surjective ];
    · aesop;
    · simp +contextual [ funext_iff, Sum.forall ]

/-
A positive subspace of the bottom-right block embeds into the block-diagonal
matrix, so `posIndex D ≤ posIndex (diag M D)`.
-/
theorem posIndex_le_fromBlocks_right (M : Matrix ι ι ℝ) (D : Matrix κ κ ℝ) :
    posIndex D ≤ posIndex (fromBlocks M 0 0 D) := by
  by_contra h;
  obtain ⟨W, hW⟩ : ∃ W : Submodule ℝ (κ → ℝ), Module.finrank ℝ W = posIndex D ∧ IsPosSubspace D W := exists_posIndex D;
  -- Let `e : (κ → ℝ) →ₗ[ℝ] (ι ⊕ κ → ℝ)` be `y ↦ Sum.elim 0 y` (injective).
  set e : (κ → ℝ) →ₗ[ℝ] (ι ⊕ κ → ℝ) := LinearMap.pi (fun i => match i with | Sum.inl _ => 0 | Sum.inr k => LinearMap.proj k);
  -- Let `V = W.map e`. Its elements are `Sum.elim 0 y`, `y ∈ W`; nonzero implies `y ≠ 0`; by `fromBlocks_diag_quadForm` the form is `0 ⬝ᵥ M *ᵥ 0 + y ⬝ᵥ D *ᵥ y = y ⬝ᵥ D *ᵥ y > 0`.
  have hV : IsPosSubspace (fromBlocks M 0 0 D) (Submodule.map e W) := by
    intro x hx;
    obtain ⟨ y, hy, rfl ⟩ := hx;
    convert hW.2 y hy using 1;
    · simp +decide [ funext_iff, e ];
    · simp +decide [ e, Matrix.mulVec, dotProduct ];
  refine' h ( le_trans _ ( finrank_le_posIndex hV ) );
  rw [ ← hW.1, LinearEquiv.finrank_eq ( show W ≃ₗ[ℝ] Submodule.map e W from ?_ ) ];
  refine' ( LinearEquiv.ofBijective _ ⟨ _, _ ⟩ );
  refine' { toFun := fun x => ⟨ e x, Submodule.mem_map_of_mem x.2 ⟩, map_add' := _, map_smul' := _ };
  all_goals norm_num [ Function.Injective, Function.Surjective ];
  intro x hx y hy hxy; ext i; replace hxy := congr_fun hxy ( Sum.inr i ) ; aesop;

/-
General upper bound: a positive subspace of `diag M D` projects (along the
second block) onto a positive subspace of `M` with kernel of dimension at most
`card κ`, so `posIndex (diag M D) ≤ posIndex M + card κ`.
-/
theorem posIndex_fromBlocks_le (M : Matrix ι ι ℝ) (D : Matrix κ κ ℝ) :
    posIndex (fromBlocks M 0 0 D) ≤ posIndex M + Fintype.card κ := by
  obtain ⟨ V, hV₁, hV₂ ⟩ := exists_posIndex ( fromBlocks M 0 0 D );
  -- Define the linear map `f : V →ₗ[ℝ] (κ → ℝ)` sending `v ↦ (v : ι ⊕ κ → ℝ) ∘ Sum.inr` (the second-block part).
  set f : V →ₗ[ℝ] (κ → ℝ) := (LinearMap.funLeft ℝ ℝ Sum.inr).comp V.subtype;
  -- The range is a submodule of `(κ → ℝ)`, so `Module.finrank ℝ (LinearMap.range f) ≤ Fintype.card κ`.
  have h_range : Module.finrank ℝ (LinearMap.range f) ≤ Fintype.card κ := by
    exact le_trans ( Submodule.finrank_le _ ) ( by simp +decide );
  -- For the kernel: every `v ∈ ker f` has its `Sum.inr` part zero, so as a function `ι ⊕ κ → ℝ` it equals `Sum.elim x 0` where `x := (v : ι⊕κ→ℝ) ∘ Sum.inl`.
  have h_kernel : ∀ v ∈ LinearMap.ker f, ∃ x : ι → ℝ, v.val = Sum.elim x 0 := by
    simp +zetaDelta at *;
    intro a ha h; use fun i => a ( Sum.inl i ) ; ext i; cases i <;> simp_all +decide [ funext_iff ] ;
  -- Define `p : (LinearMap.ker f) →ₗ[ℝ] (ι → ℝ)`, `w ↦ (w : ι⊕κ→ℝ) ∘ Sum.inl`.
  obtain ⟨p, hp⟩ : ∃ p : (LinearMap.ker f) →ₗ[ℝ] (ι → ℝ), ∀ w : LinearMap.ker f, p w = (w.val : ι ⊕ κ → ℝ) ∘ Sum.inl := by
    refine' ⟨ _, _ ⟩;
    refine' { .. };
    use fun w => w.val.val ∘ Sum.inl;
    all_goals simp +decide [ funext_iff ];
  -- The range of `p` is a positive subspace of `M`.
  have h_range_p : IsPosSubspace M (LinearMap.range p) := by
    intro x hx hx'; obtain ⟨ w, rfl ⟩ := hx; simp_all +decide [ IsPosSubspace ] ;
    convert hV₂ _ w.1.2 _ using 1;
    · convert fromBlocks_diag_quadForm M D ( w.1.val ∘ Sum.inl ) 0 |> Eq.symm using 1;
      · simp +decide [ dotProduct ];
      · obtain ⟨ x, hx ⟩ := h_kernel _ w.1.2 w.2; aesop;
    · exact fun h => hx' <| by ext i; simp +decide [ h ] ;
  -- So `Module.finrank ℝ (ker f) = Module.finrank ℝ (LinearMap.range p)` (injective).
  have h_finrank_ker : Module.finrank ℝ (LinearMap.ker f) = Module.finrank ℝ (LinearMap.range p) := by
    rw [ LinearMap.finrank_range_of_inj ];
    intro w₁ w₂ h_eq; simp_all +decide [ funext_iff, Sum.forall ] ;
    ext x; cases x <;> simp_all +decide ;
  linarith [ LinearMap.finrank_range_add_finrank_ker f, finrank_le_posIndex h_range_p ]

/-
Sharp upper bound when the bottom block is negative definite: the projection
onto the first block is injective on any positive subspace, so
`posIndex (diag M D) ≤ posIndex M`.
-/
theorem posIndex_fromBlocks_negDef_le (M : Matrix ι ι ℝ) (D : Matrix κ κ ℝ)
    (hD : ∀ y : κ → ℝ, y ≠ 0 → y ⬝ᵥ D *ᵥ y < 0) :
    posIndex (fromBlocks M 0 0 D) ≤ posIndex M := by
  obtain ⟨ V, hV₁, hV₂ ⟩ := exists_posIndex ( fromBlocks M 0 0 D );
  -- The projection onto the first block is injective on any positive subspace, so `posIndex (diag M D) ≤ posIndex M`.
  have h_proj_inj : Function.Injective (fun v : V => (fun i => v.val (Sum.inl i)) : V → (ι → ℝ)) := by
    intro v w hvw
    have h_eq : ∀ i : ι, v.val (Sum.inl i) = w.val (Sum.inl i) := by
      exact fun i => congr_fun hvw i
    have h_eq' : ∀ i : κ, v.val (Sum.inr i) = w.val (Sum.inr i) := by
      contrapose! hD;
      refine' ⟨ fun i => v.val ( Sum.inr i ) - w.val ( Sum.inr i ), _, _ ⟩ <;> simp_all +decide [ funext_iff, Matrix.mulVec, dotProduct ];
      · exact hD.imp fun i hi => sub_ne_zero_of_ne hi;
      · have := hV₂ ( v - w ) ( V.sub_mem v.2 w.2 ) ?_ <;> simp_all +decide [ Matrix.mulVec, dotProduct ];
        · linarith;
        · exact fun h => hD.elim fun i hi => hi <| by simpa [ sub_eq_zero ] using congr_fun h ( Sum.inr i ) ;
    have h_eq'' : v.val = w.val := by
      ext i; cases i <;> simp +decide [ * ] ;
    exact Subtype.ext h_eq'';
  -- The range of the projection is a positive subspace of `M`.
  have h_proj_pos : IsPosSubspace M (Submodule.map (show V →ₗ[ℝ] (ι → ℝ) from {toFun := fun v => (fun i => v.val (Sum.inl i)), map_add' := by
                                                                                aesop, map_smul' := by
                                                                                aesop}) (⊤ : Submodule ℝ V)) := by
                                                                                intro x hx;
                                                                                obtain ⟨ v, hv, rfl ⟩ := hx;
                                                                                intro hv_nonzero
                                                                                have h_quad_form : (v.val ⬝ᵥ (fromBlocks M 0 0 D) *ᵥ v.val) = (v.val ∘ Sum.inl) ⬝ᵥ M *ᵥ (v.val ∘ Sum.inl) + (v.val ∘ Sum.inr) ⬝ᵥ D *ᵥ (v.val ∘ Sum.inr) := by
                                                                                  convert fromBlocks_diag_quadForm M D ( v.val ∘ Sum.inl ) ( v.val ∘ Sum.inr ) using 1;
                                                                                  congr! 2;
                                                                                  · ext i; cases i <;> rfl;
                                                                                  · exact funext fun x => by cases x <;> rfl;
                                                                                have := hV₂ v v.2;
                                                                                by_cases h : ( v : ι ⊕ κ → ℝ ) ∘ Sum.inr = 0 <;> simp_all +decide;
                                                                                · exact this ( by rintro rfl; exact hv_nonzero <| by ext; simp +decide );
                                                                                · exact lt_of_not_ge fun h' => not_le_of_gt ( this ( by aesop ) ) ( add_nonpos h' ( le_of_lt ( hD _ h ) ) )
  generalize_proofs at *;
  convert finrank_le_posIndex h_proj_pos using 1;
  rw [ ← hV₁, Submodule.map_top ];
  rw [ LinearMap.finrank_range_of_inj ];
  exact h_proj_inj

/-- Inertia of a block-diagonal matrix with negative-definite bottom block. -/
theorem posIndex_fromBlocks_negDef (M : Matrix ι ι ℝ) (D : Matrix κ κ ℝ)
    (hD : ∀ y : κ → ℝ, y ≠ 0 → y ⬝ᵥ D *ᵥ y < 0) :
    posIndex (fromBlocks M 0 0 D) = posIndex M :=
  le_antisymm (posIndex_fromBlocks_negDef_le M D hD) (posIndex_le_fromBlocks_left M D)

/-
Additivity lower bound: a positive subspace of `M` together with one of `D`
combine into a positive subspace of the block-diagonal matrix.
-/
theorem posIndex_add_le_fromBlocks (M : Matrix ι ι ℝ) (D : Matrix κ κ ℝ) :
    posIndex M + posIndex D ≤ posIndex (fromBlocks M 0 0 D) := by
  obtain ⟨V, hV⟩ := exists_posIndex M
  obtain ⟨W, hW⟩ := exists_posIndex D;
  -- Let $e : (ι ⊕ κ → ℝ) ≃ₗ[ℝ] (ι → ℝ) × (κ → ℝ)$ be `LinearEquiv.sumArrowLequivProdArrow`.
  set e : (ι ⊕ κ → ℝ) ≃ₗ[ℝ] (ι → ℝ) × (κ → ℝ) := LinearEquiv.sumArrowLequivProdArrow ι κ ℝ ℝ;
  -- Define the combined subspace $U := (V.prod W).map e.symm.toLinearMap$ (a submodule of $ι ⊕ κ → ℝ$).
  set U : Submodule ℝ (ι ⊕ κ → ℝ) := Submodule.map (e.symm.toLinearMap) (V.prod W);
  -- Claim `IsPosSubspace (fromBlocks M 0 0 D) U`: an element `u ∈ U` is `e.symm (x, y)` with `x ∈ V`, `y ∈ W`; concretely `u = Sum.elim x y`.
  have hU_pos : IsPosSubspace (fromBlocks M 0 0 D) U := by
    intro u hu
    obtain ⟨x, y, hxV, hyW, hu_eq⟩ : ∃ x : ι → ℝ, ∃ y : κ → ℝ, x ∈ V ∧ y ∈ W ∧ u = Sum.elim x y := by
      obtain ⟨ x, hx, rfl ⟩ := Submodule.mem_map.mp hu; use x.1, x.2; aesop;
    by_cases hx : x = 0 <;> by_cases hy : y = 0 <;> simp_all +decide [ fromBlocks_diag_quadForm ];
    · exact fun _ => hW.2 y hyW hy;
    · exact fun _ => hV.2 x hxV hx;
    · exact fun _ => add_pos ( hV.2 x hxV hx ) ( hW.2 y hyW hy );
  refine' le_trans _ ( finrank_le_posIndex hU_pos );
  rw [ ← hV.1, ← hW.1, LinearEquiv.finrank_map_eq ];
  rw [ ← Module.finrank_prod ];
  refine' LinearEquiv.finrank_eq ( LinearEquiv.ofBijective _ ⟨ _, _ ⟩ ) |> le_of_eq;
  refine' { toFun := fun p => ⟨ ( p.1, p.2 ), p.1.2, p.2.2 ⟩, map_add' := _, map_smul' := _ };
  all_goals simp +decide [ Function.Injective, Function.Surjective ];
  · aesop;
  · aesop;
  · exact fun a b ha hb => ⟨ ha, hb ⟩

/-
Inertia of a block-diagonal matrix with positive-definite bottom block.
-/
theorem posIndex_fromBlocks_posDef (M : Matrix ι ι ℝ) (D : Matrix κ κ ℝ)
    (hD : D.PosDef) :
    posIndex (fromBlocks M 0 0 D) = posIndex M + Fintype.card κ := by
  refine' le_antisymm ( posIndex_fromBlocks_le M D ) _;
  convert posIndex_add_le_fromBlocks M D using 1;
  rw [ posIndex_eq_card_of_posDef hD ]

-- ═══════════════════════════════════════════════════════════════════════════
-- § 5. The KKT congruence (dual-block elimination)
-- ═══════════════════════════════════════════════════════════════════════════

/-- The block-elimination congruence factor `L = [[I, 0], [Δ⁻¹ C, I]]`. -/
noncomputable def elimL [DecidableEq ι] [DecidableEq κ] (C : Matrix κ ι ℝ)
    (Δ : Matrix κ κ ℝ) : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ :=
  fromBlocks 1 0 (Δ⁻¹ * C) 1

theorem elimL_isUnit [DecidableEq ι] [DecidableEq κ] (C : Matrix κ ι ℝ) (Δ : Matrix κ κ ℝ) :
    IsUnit (elimL C Δ) := by
  refine' ⟨ ⟨ fromBlocks 1 0 ( Δ⁻¹ * C ) 1, fromBlocks 1 0 ( - ( Δ⁻¹ * C ) ) 1, _, _ ⟩, rfl ⟩ <;> simp +decide [ Matrix.fromBlocks_multiply ]

/-
**Dual-block elimination.** `Lᵀ K L = diag(P + Cᵀ Δ⁻¹ C, -Δ)`.
-/
theorem elimL_congr [DecidableEq ι] [DecidableEq κ] (P : Matrix ι ι ℝ) (C : Matrix κ ι ℝ)
    (Δ : Matrix κ κ ℝ) (hΔsymm : Δ.IsSymm) (hΔunit : IsUnit Δ) :
    (elimL C Δ)ᵀ * (fromBlocks P Cᵀ C (-Δ)) * (elimL C Δ)
      = fromBlocks (P + Cᵀ * Δ⁻¹ * C) 0 0 (-Δ) := by
  unfold elimL;
  cases hΔunit.nonempty_invertible ; simp_all +decide [ Matrix.isUnit_iff_isUnit_det ];
  simp +decide [ Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, Matrix.mul_assoc ];
  simp +decide [ Matrix.transpose_nonsing_inv, hΔsymm.eq ]

/-
═══════════════════════════════════════════════════════════════════════════
§ 6. Main results
═══════════════════════════════════════════════════════════════════════════

The positive index of the KKT matrix equals that of the reduced Hessian.
-/
theorem kkt_posIndex [DecidableEq ι] [DecidableEq κ] (P : Matrix ι ι ℝ) (C : Matrix κ ι ℝ)
    (Δ : Matrix κ κ ℝ) (hΔ : Δ.PosDef) :
    posIndex (fromBlocks P Cᵀ C (-Δ)) = posIndex (P + Cᵀ * Δ⁻¹ * C) := by
  apply Eq.symm;
  -- By congruence invariance, we have `posIndex ((elimL C Δ)ᵀ * K * (elimL C Δ)) = posIndex K`.
  have h_congr : posIndex ((elimL C Δ)ᵀ * (fromBlocks P Cᵀ C (-Δ)) * (elimL C Δ)) = posIndex (fromBlocks P Cᵀ C (-Δ)) := by
    exact posIndex_congr _ ( elimL_isUnit C Δ );
  convert h_congr using 1;
  rw [ elimL_congr ];
  · apply Eq.symm; exact (posIndex_fromBlocks_negDef (P + Cᵀ * Δ⁻¹ * C) (-Δ) (by
    have := hΔ.2;
    simp_all +decide [ Matrix.mulVec, dotProduct, Finsupp.sum_fintype ];
    intro y hy; specialize this ( show ( Finsupp.equivFunOnFinite.symm y ) ≠ 0 from by simpa [ Finsupp.ext_iff, funext_iff ] using hy ) ; simp_all +decide [ mul_assoc, Finset.mul_sum _ _ _ ] ;));
  · exact hΔ.1;
  · grind +suggestions

/-
The negative index of the KKT matrix equals the negative index of the reduced
Hessian plus the number of dual variables.
-/
theorem kkt_negIndex [DecidableEq ι] [DecidableEq κ] (P : Matrix ι ι ℝ) (C : Matrix κ ι ℝ)
    (Δ : Matrix κ κ ℝ) (hΔ : Δ.PosDef) :
    negIndex (fromBlocks P Cᵀ C (-Δ))
      = negIndex (P + Cᵀ * Δ⁻¹ * C) + Fintype.card κ := by
  -- Using the congruence `elimL`, we can rewrite `posIndex (-K)` as `posIndex (fromBlocks (-Schur) 0 0 Δ)`.
  have h_congr : posIndex (-(fromBlocks P Cᵀ C (-Δ))) = posIndex (fromBlocks (-(P + Cᵀ * Δ⁻¹ * C)) 0 0 Δ) := by
    rw [ ← posIndex_congr _ ( elimL_isUnit C Δ ) ];
    convert congr_arg posIndex ( neg_neg ( ( elimL C Δ )ᵀ * ( fromBlocks P Cᵀ C ( -Δ ) ) * elimL C Δ ) ▸ congr_arg Neg.neg ( elimL_congr P C Δ hΔ.1 hΔ.isUnit ) ) using 1;
    · simp +decide [ Matrix.mul_assoc ];
    · congr ; ext i j ; cases i <;> cases j <;> simp +decide [ Matrix.neg_apply ];
  convert posIndex_fromBlocks_posDef ( - ( P + Cᵀ * Δ⁻¹ * C ) ) Δ hΔ using 1

/-
**Inertia of the dual-regularized KKT system.**

With the dual regularization `Δ` symmetric positive definite, the KKT matrix
`[[P, Cᵀ], [C, -Δ]]` has inertia `(card ι, card κ, 0)` — full positive index on
the primal block, full negative index on the dual block, and no zero directions —
**iff** the reduced (Schur-complement) Hessian `P + Cᵀ Δ⁻¹ C` is positive definite.
-/
theorem kkt_inertia_iff [DecidableEq ι] [DecidableEq κ] (P : Matrix ι ι ℝ) (C : Matrix κ ι ℝ)
    (Δ : Matrix κ κ ℝ) (hP : P.IsHermitian) (hΔ : Δ.PosDef) :
    HasInertia (fromBlocks P Cᵀ C (-Δ)) (Fintype.card ι) (Fintype.card κ) 0
      ↔ (P + Cᵀ * Δ⁻¹ * C).PosDef := by
  constructor;
  · intro h
    have h_posIndex : posIndex (P + Cᵀ * Δ⁻¹ * C) = Fintype.card ι := by
      rw [ ← kkt_posIndex P C Δ hΔ, h.1 ]
    have h_posDef : (P + Cᵀ * Δ⁻¹ * C).PosDef := by
      apply posDef_of_posIndex_eq_card;
      · simp_all +decide [ Matrix.IsHermitian, Matrix.mul_assoc ];
        have := hΔ.1; simp_all +decide [ Matrix.IsHermitian, Matrix.transpose_nonsing_inv ] ;
      · exact h_posIndex
    exact h_posDef;
  · intro hSchur
    have h_posIndex : posIndex (fromBlocks P Cᵀ C (-Δ)) = Fintype.card ι := by
      rw [ kkt_posIndex P C Δ hΔ, posIndex_eq_card_of_posDef hSchur ]
    have h_negIndex : negIndex (fromBlocks P Cᵀ C (-Δ)) = Fintype.card κ := by
      have h_negIndex : negIndex (P + Cᵀ * Δ⁻¹ * C) = 0 := by
        unfold negIndex
        apply posIndex_eq_zero_of_neg
        intro x hx
        have hpos := (Matrix.posDef_iff_dotProduct_mulVec.mp hSchur).2 hx
        simp only [star_trivial] at hpos
        have hneg : x ⬝ᵥ (-(P + Cᵀ * Δ⁻¹ * C)) *ᵥ x
            = -(x ⬝ᵥ (P + Cᵀ * Δ⁻¹ * C) *ᵥ x) := by
          rw [Matrix.neg_mulVec, dotProduct_neg]
        rw [hneg]
        linarith [hpos]
      rw [ kkt_negIndex P C Δ hΔ, h_negIndex, zero_add ]
    exact ⟨h_posIndex, h_negIndex, by simp⟩

/-- **Inertia of the dual-regularized LQR first-order system, with explicit
stage/state/control counts.**

For a dual-regularized LQR problem with `N` stages, `n`-dimensional states and
`m`-dimensional controls, the primal block has dimension `N*(n+m)+n`
(`(N+1)` states of size `n` plus `N` controls of size `m`) and the dual block has
dimension `(N+1)*n` (the initial-state constraint plus `N` dynamics constraints).

With `Δ` symmetric positive definite, the first-order (KKT) matrix
`[[P, Cᵀ], [C, -Δ]]` has inertia `(N*(n+m)+n, (N+1)*n, 0)` **iff** the reduced
(Schur-complement) Hessian `P + Cᵀ Δ⁻¹ C` — the matrix factorized by the sequential
dual-regularized Riccati backward pass — is positive definite. -/
theorem kkt_inertia_iff_lqr {N n m : ℕ}
    (P : Matrix (Fin (N * (n + m) + n)) (Fin (N * (n + m) + n)) ℝ)
    (C : Matrix (Fin ((N + 1) * n)) (Fin (N * (n + m) + n)) ℝ)
    (Δ : Matrix (Fin ((N + 1) * n)) (Fin ((N + 1) * n)) ℝ)
    (hP : P.IsHermitian) (hΔ : Δ.PosDef) :
    HasInertia (fromBlocks P Cᵀ C (-Δ)) (N * (n + m) + n) ((N + 1) * n) 0
      ↔ (P + Cᵀ * Δ⁻¹ * C).PosDef := by
  simpa [Fintype.card_fin] using kkt_inertia_iff P C Δ hP hΔ

end KKTInertia