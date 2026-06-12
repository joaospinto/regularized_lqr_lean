/-
# Residual Computation: the paper's residual formulas *are* the Newton–KKT product

The paper's **Residual Computation** section (specialized to discrete-time
optimal control, `\cref{optimal-control-specialization}`) writes the residual of
the Newton–KKT linear system

```
  [ P    Cᵀ ] [ x ]   [ s ]
  [ C   -Δ  ] [ y ] + [ c ]
```

as an explicit, stage-structured vector:

```
  [ Qᵢ xᵢ + Mᵢ uᵢ + Aᵢᵀ y_{i+1} + qᵢ − yᵢ ]_{i=0,…,N-1}
  [ Mᵢᵀ xᵢ + Rᵢ uᵢ + Bᵢᵀ y_{i+1} + rᵢ      ]_{i=0,…,N-1}
  [ Q_N x_N + q_N − y_N                      ]
  [ c₀ − Δ₀ y₀ − x₀                          ]
  [ Aᵢ xᵢ + Bᵢ uᵢ + c_{i+1} − Δ_{i+1} y_{i+1} − x_{i+1} ]_{i=0,…,N-1}
```

The paper states no theorem here — but there is an *implicit* one: these explicit
formulas must equal the matrix–vector product of the Newton–KKT matrix with the
stacked iterate `[x; y]`, plus the stacked right-hand side `[s; c]`.  This file
makes that precise and proves it.

We assemble the genuine KKT matrix `[[P, Cᵀ], [C, -Δ]]` from the `DualRegLQR`
problem data as a block matrix over stage-structured index types, form the
stacked solution and right-hand side, define the residual as the literal product
`K *ᵥ [x;y] + [s;c]`, and prove (`residual_state`, `residual_state_terminal`,
`residual_control`, `residual_dual_initial`, `residual_dual_dynamics`) that each
component equals the corresponding paper formula.
-/
import Mathlib
import RequestProject.DualRegLQR

open Matrix

namespace ResidualComputation

variable {n m N : ℕ}

/-- State index: stage `i ∈ {0,…,N}` together with a state coordinate. -/
abbrev St (N n : ℕ) := Fin (N + 1) × Fin n
/-- Control index: stage `i ∈ {0,…,N-1}` together with a control coordinate. -/
abbrev Ct (N m : ℕ) := Fin N × Fin m
/-- Primal index: states followed by controls. -/
abbrev Pr (N n m : ℕ) := St N n ⊕ Ct N m
/-- Dual index: one block per constraint (initial state + `N` dynamics). -/
abbrev Du (N n : ℕ) := Fin (N + 1) × Fin n

-- ═══════════════════════════════════════════════════════════════════════════
-- § Stacked vectors
-- ═══════════════════════════════════════════════════════════════════════════

/-- Stack a stagewise state trajectory into a single vector over `St`. -/
def stateVec (x : Fin (N + 1) → Fin n → ℝ) : St N n → ℝ := fun p => x p.1 p.2
/-- Stack a stagewise control trajectory into a single vector over `Ct`. -/
def ctrlVec (u : Fin N → Fin m → ℝ) : Ct N m → ℝ := fun p => u p.1 p.2
/-- Stack the dual variables into a single vector over `Du`. -/
def dualVec (y : Fin (N + 1) → Fin n → ℝ) : Du N n → ℝ := fun p => y p.1 p.2

/-- The stacked primal iterate `[x; u]`. -/
def primVec (x : Fin (N + 1) → Fin n → ℝ) (u : Fin N → Fin m → ℝ) : Pr N n m → ℝ :=
  Sum.elim (stateVec x) (ctrlVec u)

-- ═══════════════════════════════════════════════════════════════════════════
-- § Blocks of the primal Hessian `P` (block-diagonal over stages)
-- ═══════════════════════════════════════════════════════════════════════════

/-- State–state block of `P`: block diagonal with `Qᵢ`. -/
def Pxx (prob : DualRegLQR n m N) : Matrix (St N n) (St N n) ℝ :=
  Matrix.of fun p q => if p.1 = q.1 then prob.Q p.1 p.2 q.2 else 0

/-- State–control block of `P`: block diagonal with `Mᵢ` (only for `i < N`). -/
def Pxu (prob : DualRegLQR n m N) : Matrix (St N n) (Ct N m) ℝ :=
  Matrix.of fun p q => if p.1.val = q.1.val then prob.Mcross q.1 p.2 q.2 else 0

/-- Control–control block of `P`: block diagonal with `Rᵢ`. -/
def Puu (prob : DualRegLQR n m N) : Matrix (Ct N m) (Ct N m) ℝ :=
  Matrix.of fun p q => if p.1 = q.1 then prob.R p.1 p.2 q.2 else 0

/-- The primal Hessian `P = [[Q, M], [Mᵀ, R]]` (block diagonal over stages). -/
def Pmat (prob : DualRegLQR n m N) : Matrix (Pr N n m) (Pr N n m) ℝ :=
  fromBlocks (Pxx prob) (Pxu prob) (Pxu prob)ᵀ (Puu prob)

-- ═══════════════════════════════════════════════════════════════════════════
-- § The dual regularization `Δ` (block-diagonal over constraints)
-- ═══════════════════════════════════════════════════════════════════════════

/-- The dual regularization matrix `Δ`: block diagonal with `Δᵢ`. -/
def Dmat (prob : DualRegLQR n m N) : Matrix (Du N n) (Du N n) ℝ :=
  Matrix.of fun p q => if p.1 = q.1 then prob.Delta p.1 p.2 q.2 else 0

-- ═══════════════════════════════════════════════════════════════════════════
-- § The constraint Jacobian `C`
-- ═══════════════════════════════════════════════════════════════════════════

/-- State columns of the constraint matrix `C`.  Constraint `i` reads
`−xᵢ` (the `−I` diagonal) and, for `i = k+1`, `Aₖ x_k`. -/
def CXmat (prob : DualRegLQR n m N) : Matrix (Du N n) (St N n) ℝ :=
  Matrix.of fun d s =>
    (if d = s then (-1 : ℝ) else 0)
      + (if h : s.1.val + 1 = d.1.val then prob.A ⟨s.1.val, by omega⟩ d.2 s.2 else 0)

/-- Control columns of the constraint matrix `C`.  Constraint `i = k+1` reads
`Bₖ u_k`. -/
def CUmat (prob : DualRegLQR n m N) : Matrix (Du N n) (Ct N m) ℝ :=
  Matrix.of fun d s => if s.1.val + 1 = d.1.val then prob.B s.1 d.2 s.2 else 0

/-- The constraint Jacobian `C` (rows: constraints, columns: primal variables). -/
def Cmat (prob : DualRegLQR n m N) : Matrix (Du N n) (Pr N n m) ℝ :=
  Matrix.of fun d p => Sum.elim (fun s => CXmat prob d s) (fun s => CUmat prob d s) p

-- ═══════════════════════════════════════════════════════════════════════════
-- § The Newton–KKT matrix, stacked RHS, and the residual
-- ═══════════════════════════════════════════════════════════════════════════

/-- The Newton–KKT matrix `K = [[P, Cᵀ], [C, -Δ]]`. -/
def Kmat (prob : DualRegLQR n m N) : Matrix (Pr N n m ⊕ Du N n) (Pr N n m ⊕ Du N n) ℝ :=
  fromBlocks (Pmat prob) (Cmat prob)ᵀ (Cmat prob) (-(Dmat prob))

/-- The stacked right-hand side `[s; c]`, where `s = [q; r]`. -/
def rhsVec (prob : DualRegLQR n m N) : Pr N n m ⊕ Du N n → ℝ :=
  Sum.elim
    (Sum.elim (fun p => prob.qvec p.1 p.2) (fun p => prob.rvec p.1 p.2))
    (fun d => prob.cvec d.1 d.2)

/-- The residual of the Newton–KKT system at iterate `(x, u, y)`:
`r = K · [x; y] + [s; c]`. -/
def kktResidual (prob : DualRegLQR n m N)
    (x : Fin (N + 1) → Fin n → ℝ) (u : Fin N → Fin m → ℝ) (y : Fin (N + 1) → Fin n → ℝ) :
    Pr N n m ⊕ Du N n → ℝ :=
  Kmat prob *ᵥ Sum.elim (primVec x u) (dualVec y) + rhsVec prob

-- ═══════════════════════════════════════════════════════════════════════════
-- § Block mul-vec helper lemmas
-- ═══════════════════════════════════════════════════════════════════════════

variable (prob : DualRegLQR n m N)
  (x : Fin (N + 1) → Fin n → ℝ) (u : Fin N → Fin m → ℝ) (y : Fin (N + 1) → Fin n → ℝ)

lemma Pxx_mulVec (i : Fin (N + 1)) (a : Fin n) :
    (Pxx prob *ᵥ stateVec x) (i, a) = (prob.Q i *ᵥ x i) a := by
  unfold Pxx; simp +decide [ Fintype.sum_prod_type, dotProduct, Matrix.mulVec ]
  rfl

lemma Puu_mulVec (j : Fin N) (a : Fin m) :
    (Puu prob *ᵥ ctrlVec u) (j, a) = (prob.R j *ᵥ u j) a := by
  unfold Puu; simp +decide [ Fintype.sum_prod_type, dotProduct, Matrix.mulVec ]
  rfl

lemma Pxu_mulVec_interior (i : Fin (N + 1)) (hi : i.val < N) (a : Fin n) :
    (Pxu prob *ᵥ ctrlVec u) (i, a) = (prob.Mcross ⟨i.val, hi⟩ *ᵥ u ⟨i.val, hi⟩) a := by
  simp +decide [ Fintype.sum_prod_type, Matrix.mulVec, dotProduct, Pxu, ctrlVec ]
  rw [ Finset.sum_eq_single ⟨ i, hi ⟩ ] <;> aesop

lemma Pxu_mulVec_terminal (a : Fin n) :
    (Pxu prob *ᵥ ctrlVec u) (⟨N, by omega⟩, a) = 0 := by
  unfold Pxu; simp +decide [ Fintype.sum_prod_type, dotProduct, Matrix.mulVec ]
  exact Finset.sum_eq_zero fun i hi => if_neg <| ne_of_gt <| Fin.is_lt i

lemma PxuT_mulVec (j : Fin N) (a : Fin m) :
    ((Pxu prob)ᵀ *ᵥ stateVec x) (j, a)
      = ((prob.Mcross j)ᵀ *ᵥ x ⟨j.val, by omega⟩) a := by
  unfold Pxu; simp +decide [ Fintype.sum_prod_type, dotProduct, Matrix.mulVec ]
  rw [ Finset.sum_eq_single ⟨ j, by linarith [ Fin.is_lt j ] ⟩ ] <;> simp_all +decide [ Fin.ext_iff ]
  rfl

lemma Dmat_mulVec (i : Fin (N + 1)) (a : Fin n) :
    (Dmat prob *ᵥ dualVec y) (i, a) = (prob.Delta i *ᵥ y i) a := by
  unfold Dmat; simp +decide [ Fintype.sum_prod_type, dotProduct, Matrix.mulVec ]
  rfl

/-- `Cᵀ` acting on the duals, at a state row `i < N`: `Aᵢᵀ y_{i+1} − yᵢ`. -/
lemma CmatT_mulVec_state_interior (i : Fin (N + 1)) (hi : i.val < N) (a : Fin n) :
    ((Cmat prob)ᵀ *ᵥ dualVec y) (Sum.inl (i, a))
      = ((prob.A ⟨i.val, hi⟩)ᵀ *ᵥ y ⟨i.val + 1, by omega⟩ - y i) a := by
  simp +decide [ Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Sum.elim_inl, 
    Cmat, CXmat, CUmat ]
  rw [ Finset.sum_eq_add ( i ) ( ⟨ i.val + 1, by linarith ⟩ : Fin ( N + 1 ) ) ] <;> norm_num
  · simp +decide [ Fin.ext_iff, dualVec ]; ring!
  · exact ne_of_lt ( Nat.lt_succ_self _ )
  · intro c hc₁ hc₂; rw [ Finset.sum_eq_zero ]; intros; aesop

/-- `Cᵀ` acting on the duals, at the terminal state row `i = N`: `−y_N`. -/
lemma CmatT_mulVec_state_terminal (a : Fin n) :
    ((Cmat prob)ᵀ *ᵥ dualVec y) (Sum.inl (⟨N, by omega⟩, a))
      = (- y ⟨N, by omega⟩) a := by
  unfold Cmat; simp +decide [ Fintype.sum_prod_type, dotProduct, Matrix.mulVec ]
  unfold CXmat; simp +decide [   ]
  rw [ Finset.sum_eq_single ⟨ N, by omega ⟩ ] <;> simp_all +decide [ Fin.ext_iff ]
  · rw [ Finset.sum_eq_single a ] <;> simp +contextual [ dualVec ]
    exact fun b hb h => False.elim <| hb <| Fin.ext h
  · omega

/-- `Cᵀ` acting on the duals, at a control row `j`: `Bⱼᵀ y_{j+1}`. -/
lemma CmatT_mulVec_control (j : Fin N) (a : Fin m) :
    ((Cmat prob)ᵀ *ᵥ dualVec y) (Sum.inr (j, a))
      = ((prob.B j)ᵀ *ᵥ y ⟨j.val + 1, by omega⟩) a := by
  unfold Cmat dualVec; simp +decide [ Matrix.mulVec, dotProduct, Fintype.sum_prod_type ]
  rw [ Finset.sum_eq_single ⟨ j.val + 1, by linarith [ Fin.is_lt j ] ⟩ ] <;> simp +decide [ CUmat ]
  exact fun k hk₁ hk₂ => False.elim <| hk₁ <| Fin.ext hk₂.symm

/-- `C` acting on the primal iterate, at the initial constraint `i = 0`: `−x₀`. -/
lemma Cmat_mulVec_initial (a : Fin n) :
    (Cmat prob *ᵥ primVec x u) (⟨0, by omega⟩, a) = (- x ⟨0, by omega⟩) a := by
  simp_all +decide [ Matrix.mulVec,  primVec,  Cmat, CXmat, CUmat ]
  simp +decide [ stateVec, dotProduct ]

/-- `C` acting on the primal iterate, at dynamics constraint `i = k+1`:
`Aₖ x_k + Bₖ u_k − x_{k+1}`. -/
lemma Cmat_mulVec_dynamics (k : Fin N) (a : Fin n) :
    (Cmat prob *ᵥ primVec x u) (⟨k.val + 1, by omega⟩, a)
      = (prob.A k *ᵥ x ⟨k.val, by omega⟩ + prob.B k *ᵥ u k - x ⟨k.val + 1, by omega⟩) a := by
  unfold Cmat primVec; simp +decide [ Matrix.mulVec]
  unfold CXmat CUmat stateVec ctrlVec
  simp +decide [ Fintype.sum_prod_type, dotProduct, Finset.sum_add_distrib, add_mul,  sub_eq_add_neg ]
  rw [ Finset.sum_eq_single ⟨ k, by linarith [ Fin.is_lt k ] ⟩, Finset.sum_eq_single k ] <;>
    simp +decide [ Fin.ext_iff ]
  ring!
  · aesop
  · aesop

-- ═══════════════════════════════════════════════════════════════════════════
-- § Main theorems: the residual formulas are the KKT matrix product
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Residual, interior state row** (`0 ≤ i < N`):
`Qᵢ xᵢ + Mᵢ uᵢ + Aᵢᵀ y_{i+1} + qᵢ − yᵢ`. -/
theorem residual_state (i : Fin (N + 1)) (hi : i.val < N) (a : Fin n) :
    kktResidual prob x u y (Sum.inl (Sum.inl (i, a)))
      = (prob.Q i *ᵥ x i + prob.Mcross ⟨i.val, hi⟩ *ᵥ u ⟨i.val, hi⟩
          + (prob.A ⟨i.val, hi⟩)ᵀ *ᵥ y ⟨i.val + 1, by omega⟩ + prob.qvec i - y i) a := by
  unfold kktResidual
  have h_mul : (Kmat prob *ᵥ (primVec x u ⊕ᵥ dualVec y)) (Sum.inl (Sum.inl (i, a)))
      = (Pmat prob *ᵥ (primVec x u)) (Sum.inl (i, a))
        + ((Cmat prob)ᵀ *ᵥ (dualVec y)) (Sum.inl (i, a)) := by
    unfold Kmat; simp +decide [ Fintype.sum_sum_type, dotProduct, Matrix.mulVec ]
  have h_mul_P : (Pmat prob *ᵥ (primVec x u)) (Sum.inl (i, a))
      = (Pxx prob *ᵥ stateVec x) (i, a) + (Pxu prob *ᵥ ctrlVec u) (i, a) := by
    unfold Pmat
    simp +decide [ Matrix.mulVec,  primVec]
    simp +decide [ dotProduct,   fromBlocks ]
  simp_all +decide [ Pxx_mulVec, Pxu_mulVec_interior, CmatT_mulVec_state_interior, rhsVec ]
  ring

/-- **Residual, terminal state row** (`i = N`): `Q_N x_N + q_N − y_N`. -/
theorem residual_state_terminal (a : Fin n) :
    kktResidual prob x u y (Sum.inl (Sum.inl (⟨N, by omega⟩, a)))
      = (prob.Q ⟨N, by omega⟩ *ᵥ x ⟨N, by omega⟩ + prob.qvec ⟨N, by omega⟩
          - y ⟨N, by omega⟩) a := by
  convert Pxx_mulVec prob x ⟨ N, by linarith ⟩ a |> congrArg
    ( · + ( prob.qvec ⟨ N, by linarith ⟩ a )
        + ( ( Cmat prob )ᵀ *ᵥ ( dualVec y ) ) ( Sum.inl ( ⟨ N, by linarith ⟩, a ) ) ) using 1
  ring!
  · unfold kktResidual; unfold Kmat; simp +decide [ Fintype.sum_sum_type, dotProduct, Matrix.mulVec ]
    unfold Pmat primVec stateVec ctrlVec
    simp +decide [   ]
    ring!
    unfold Pxu; simp +decide [ Fintype.sum_prod_type]
    exact Finset.sum_eq_zero fun i hi => if_neg <| ne_of_gt <| Fin.is_lt i
  · rw [ CmatT_mulVec_state_terminal ]; ring!
    norm_num [ sub_eq_add_neg ]

/-- **Residual, control row** (`0 ≤ j < N`):
`Mⱼᵀ xⱼ + Rⱼ uⱼ + Bⱼᵀ y_{j+1} + rⱼ`. -/
theorem residual_control (j : Fin N) (a : Fin m) :
    kktResidual prob x u y (Sum.inl (Sum.inr (j, a)))
      = ((prob.Mcross j)ᵀ *ᵥ x ⟨j.val, by omega⟩ + prob.R j *ᵥ u j
          + (prob.B j)ᵀ *ᵥ y ⟨j.val + 1, by omega⟩ + prob.rvec j) a := by
  unfold kktResidual; unfold Kmat; simp +decide [ Fintype.sum_sum_type, dotProduct, Matrix.mulVec ]
  unfold Pmat Cmat primVec dualVec rhsVec
  simp +decide [   ]
  congr! 2
  · unfold Pxu; simp +decide [ Fintype.sum_prod_type]
    rw [ Finset.sum_eq_single ⟨ j, by linarith [ Fin.is_lt j ] ⟩ ] <;> simp +decide [ Fin.ext_iff ]
    · rfl
    · aesop
  · unfold Puu ctrlVec; simp +decide [ Fintype.sum_prod_type]
  · unfold CUmat; simp +decide [ Fintype.sum_prod_type]
    rw [ Finset.sum_eq_single ⟨ j + 1, by linarith [ Fin.is_lt j ] ⟩ ] <;> aesop

/-- **Residual, initial-state constraint row** (`i = 0`): `c₀ − Δ₀ y₀ − x₀`. -/
theorem residual_dual_initial (a : Fin n) :
    kktResidual prob x u y (Sum.inr (⟨0, by omega⟩, a))
      = (prob.cvec ⟨0, by omega⟩ - prob.Delta ⟨0, by omega⟩ *ᵥ y ⟨0, by omega⟩
          - x ⟨0, by omega⟩) a := by
  convert Cmat_mulVec_initial prob x u a |> congrArg
    ( · + ( prob.cvec ⟨ 0, by linarith ⟩ a )
        + ( ( - ( Dmat prob ) ) *ᵥ ( dualVec y ) ) ( ⟨ 0, by linarith ⟩, a ) ) using 1
  ring!
  · unfold kktResidual; unfold Kmat
    simp +decide [ Fintype.sum_sum_type, dotProduct, Matrix.mulVec ]; ring!
  · simp +decide [ Dmat_mulVec, Matrix.neg_mulVec ]; ring!

/-- **Residual, dynamics constraint row** (`i = k+1`):
`Aₖ x_k + Bₖ u_k + c_{k+1} − Δ_{k+1} y_{k+1} − x_{k+1}`. -/
theorem residual_dual_dynamics (k : Fin N) (a : Fin n) :
    kktResidual prob x u y (Sum.inr (⟨k.val + 1, by omega⟩, a))
      = (prob.A k *ᵥ x ⟨k.val, by omega⟩ + prob.B k *ᵥ u k
          + prob.cvec ⟨k.val + 1, by omega⟩
          - prob.Delta ⟨k.val + 1, by omega⟩ *ᵥ y ⟨k.val + 1, by omega⟩
          - x ⟨k.val + 1, by omega⟩) a := by
  have := @ResidualComputation.Cmat_mulVec_dynamics
  convert congr_arg
    ( fun z => z + ( prob.cvec ⟨ k.val + 1, by linarith [ Fin.is_lt k ] ⟩ a )
        + ( ( - ( Dmat prob ) ) *ᵥ ( dualVec y ) ) ( ⟨ k.val + 1, by linarith [ Fin.is_lt k ] ⟩, a ) )
    ( this prob x u k a ) using 1
  · unfold kktResidual; unfold Kmat
    simp +decide [ Fintype.sum_sum_type, dotProduct, Matrix.mulVec ]; ring!
  · rw [ Matrix.neg_mulVec ]; norm_num [ Dmat_mulVec, Matrix.neg_mulVec ]; ring!

end ResidualComputation
