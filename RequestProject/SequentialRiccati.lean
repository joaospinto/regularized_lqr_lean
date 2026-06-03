/-
# Sequential Riccati Recursion

This file contains the complete sequential Riccati recursion for the
dual-regularized LQR problem, including:

## § 1. Riccati Formula Definitions
- `riccatiW`: Smoothed Hessian W = P(I + ΔP)⁻¹
- `riccatiG`: Effective control cost G = R + BᵀWB
- `riccatiH`: Cross-Hessian H = BᵀWA + Sᵀ
- `riccatiK`: Optimal feedback gain K = −G⁻¹H
- `riccatiPstep`: Hessian update P = Q + AᵀWA + HᵀK

## § 2. PSD Preservation (Theorem 2)
- `riccatiW_posSemidef`: W is PSD when P, Δ are PSD
- `riccati_completing_square`: P = Q + SK + KᵀSᵀ + KᵀRK + (A+BK)ᵀW(A+BK)
- `riccati_step_posSemidef`: One-step PSD preservation
- `riccati_backward_posSemidef`: Full backward induction

## § 3. Cost-to-Go Correctness (Theorem 3)
- `completing_the_square_generic`: Generic completing-the-square lemma
- `oneStepLagrangian`: Definition of the one-step Lagrangian
- Gradient conditions verifying first-order optimality
- Completing-the-square → saddle-point conditions
- `value_identity`: Saddle-point value = Riccati cost-to-go

## § 4. Alternative p-Recurrence (Corollary)
- `p_recurrence_corollary`: pₖ = qₖ + Kₖᵀrₖ + (Aₖ + BₖKₖ)ᵀgₖ₊₁

References:
- Sousa-Pinto & Orban, "Dual-Regularized Riccati Recursions for
  Interior-Point Optimal Control"
-/
import Mathlib
import RequestProject.MatrixHelpers

open Matrix

set_option maxHeartbeats 800000

variable {n m : ℕ} [DecidableEq (Fin n)] [DecidableEq (Fin m)]

-- ═══════════════════════════════════════════════════════════════════════════
-- § 1. Riccati Formula Definitions and W PSD
-- ═══════════════════════════════════════════════════════════════════════════

/-! ### Part 1: W = P(I + ΔP)⁻¹ is PSD -/

section W_PSD

variable (P Δ : Matrix (Fin n) (Fin n) ℝ)

/-- W = P(I + ΔP)⁻¹, the "smoothed" cost-to-go Hessian -/
noncomputable def riccatiW : Matrix (Fin n) (Fin n) ℝ := P * (1 + Δ * P)⁻¹

/-- Key quadratic form identity for W:
    v^T W v = u^T P u + (Pu)^T Δ (Pu)
    where u = (I + ΔP)⁻¹ v.
    Proof: v = (I+ΔP)u, so v^T P u = u^T(I+ΔP)^T P u
    = u^T(I+PΔ)Pu (using P,Δ symmetric) = u^TPu + u^T(PΔP)u = u^TPu + (Pu)^TΔ(Pu) -/
theorem riccatiW_quadForm (hPs : P.IsSymm) (hΔs : Δ.IsSymm)
    (hInv : IsUnit (1 + Δ * P)) (v : Fin n → ℝ) :
    let u := (1 + Δ * P)⁻¹.mulVec v
    v ⬝ᵥ (riccatiW P Δ).mulVec v =
      u ⬝ᵥ P.mulVec u + (P.mulVec u) ⬝ᵥ Δ.mulVec (P.mulVec u) := by
  obtain ⟨ u, hu ⟩ := hInv.exists_left_inv;
  have h_inv : u = (1 + Δ * P)⁻¹ := by
    rw [ Matrix.inv_eq_left_inv hu ];
  have h_inv : (1 + Δ * P).mulVec ((1 + Δ * P)⁻¹.mulVec v) = v := by
    simp +decide [ ← mul_assoc, ← h_inv, hu ];
    rw [ mul_eq_one_comm.mp hu, Matrix.one_mulVec ];
  have h_inv : (1 + Δ * P).mulVec ((1 + Δ * P)⁻¹.mulVec v) = (1 + Δ * P)⁻¹.mulVec v + Δ.mulVec (P.mulVec ((1 + Δ * P)⁻¹.mulVec v)) := by
    simp +decide [ Matrix.add_mulVec, Matrix.mulVec_add ];
    simp +decide [ add_mul, mul_assoc ];
    rw [ Matrix.add_mulVec ];
  unfold riccatiW; simp_all +decide [ Matrix.mulVec_add, Matrix.mulVec_mulVec ] ;
  simp_all +decide [ ← eq_sub_iff_add_eq', dotProduct_comm ]

/-- W is symmetric when P and Δ are symmetric.
    Proof: W^T = ((I+ΔP)⁻¹)^T P = ((I+ΔP)^T)⁻¹ P = (I+PΔ)⁻¹ P = P(I+ΔP)⁻¹ = W
    using the commutation identity (I+PΔ)⁻¹P = P(I+ΔP)⁻¹ from InverseHelper. -/
theorem riccatiW_isSymm (hPs : P.IsSymm) (hΔs : Δ.IsSymm)
    (hInv1 : IsUnit (1 + Δ * P)) (hInv2 : IsUnit (1 + P * Δ)) :
    (riccatiW P Δ).IsSymm := by
  unfold riccatiW;
  simp_all +decide [ Matrix.IsSymm, Matrix.mul_assoc ];
  convert inv_mul_comm ( Δ ) ( P ) hInv2 hInv1 using 1;
  rw [ Matrix.transpose_nonsing_inv, Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_mul, hPs, hΔs ]

/-
I - WΔ = (I + PΔ)⁻¹.
    This identity (omitted from the paper for space) shows that the "residual"
    I - WΔ has a clean closed form. It also provides an alternative proof that
    W is symmetric, since (I - WΔ)^T = ((I+PΔ)⁻¹)^T = ((I+PΔ)^T)⁻¹ = (I+ΔP)⁻¹,
    and WΔ = I - (I+PΔ)⁻¹ while ΔW = I - (I+ΔP)⁻¹ (both by Lemma 2).
-/
theorem one_sub_riccatiW_mul (hInv1 : IsUnit (1 + Δ * P))
    (hInv2 : IsUnit (1 + P * Δ)) :
    1 - riccatiW P Δ * Δ = (1 + P * Δ)⁻¹ := by
  unfold riccatiW;
  grind +suggestions

/-- W is PSD when P and Δ are PSD.
    Uses the quadratic form identity: v^T W v = u^T P u + (Pu)^T Δ (Pu) ≥ 0. -/
theorem riccatiW_posSemidef (hP : P.PosSemidef) (hΔ : Δ.PosSemidef)
    (hInv1 : IsUnit (1 + Δ * P)) (hInv2 : IsUnit (1 + P * Δ)) :
    (riccatiW P Δ).PosSemidef := by
  apply posSemidef_of_symm_nonneg
  · exact riccatiW_isSymm P Δ (psd_isSymm hP) (psd_isSymm hΔ) hInv1 hInv2
  · intro v
    rw [riccatiW_quadForm P Δ (psd_isSymm hP) (psd_isSymm hΔ) hInv1]
    exact add_nonneg (psd_dotProduct_nonneg hP _) (psd_dotProduct_nonneg hΔ _)

end W_PSD

/-! ### Part 2: Completing the square -/

section CompletingSquare

variable (Q : Matrix (Fin n) (Fin n) ℝ)
variable (R : Matrix (Fin m) (Fin m) ℝ)
variable (S : Matrix (Fin n) (Fin m) ℝ)
variable (A : Matrix (Fin n) (Fin n) ℝ)
variable (B : Matrix (Fin n) (Fin m) ℝ)
variable (W : Matrix (Fin n) (Fin n) ℝ)

/-- G = R + BᵀWB, the effective control cost Hessian -/
noncomputable def riccatiG : Matrix (Fin m) (Fin m) ℝ := R + Bᵀ * W * B

/-- H = BᵀWA + Sᵀ, the cross-Hessian -/
noncomputable def riccatiH : Matrix (Fin m) (Fin n) ℝ := Bᵀ * W * A + Sᵀ

/-- K = -G⁻¹H, the optimal feedback gain -/
noncomputable def riccatiK (G : Matrix (Fin m) (Fin m) ℝ)
    (H : Matrix (Fin m) (Fin n) ℝ) : Matrix (Fin m) (Fin n) ℝ := -G⁻¹ * H

/-- The Riccati backward step for P: P_new = Q + AᵀWA + HᵀK -/
noncomputable def riccatiPstep (H : Matrix (Fin m) (Fin n) ℝ)
    (K : Matrix (Fin m) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Q + Aᵀ * W * A + Hᵀ * K

/-- Key identity: G * K + H = 0, since K = -G⁻¹H implies GK = -H. -/
theorem riccatiGK_add_H (G : Matrix (Fin m) (Fin m) ℝ)
    (H : Matrix (Fin m) (Fin n) ℝ) (hG : IsUnit G) :
    G * riccatiK G H + H = 0 := by
  unfold riccatiK; simp_all +decide [ Matrix.isUnit_iff_isUnit_det ] ;

/-- The completing-the-square matrix identity:
    P_new = Q + S*K + Kᵀ*Sᵀ + Kᵀ*R*K + (A + B*K)ᵀ * W * (A + B*K)

    Proof: RHS expands to Q + A^TWA + (S+A^TWB)K + K^T(S^T+B^TWA) + K^T(R+B^TWB)K
    = Q + A^TWA + H^TK + K^TH + K^TGK
    = Q + A^TWA + H^TK + K^T(H + GK) = Q + A^TWA + H^TK (since GK+H=0)
    = P_new. -/
theorem riccati_completing_square
    (hWs : W.IsSymm) (hG : IsUnit (riccatiG R B W)) :
    let H := riccatiH S A B W
    let K := riccatiK (riccatiG R B W) H
    riccatiPstep Q A W H K =
      Q + S * K + Kᵀ * Sᵀ + Kᵀ * R * K + (A + B * K)ᵀ * W * (A + B * K) := by
  unfold riccatiPstep riccatiH riccatiK riccatiG at *;
  simp +decide [ Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, Matrix.transpose_mul, hWs.eq ];
  have h_inv : (R + Bᵀ * W * B) * (R + Bᵀ * W * B)⁻¹ = 1 := by
    exact Matrix.mul_nonsing_inv _ ( show IsUnit ( R + Bᵀ * W * B |> Matrix.det ) from hG.map ( Matrix.detMonoidHom ) );
  simp_all +decide [ Matrix.mul_assoc, Matrix.add_mul, Matrix.mul_add, Matrix.transpose_nonsing_inv ];
  simp_all +decide [ ← Matrix.mul_assoc, ← eq_sub_iff_add_eq' ];
  simp_all +decide [ Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, Matrix.transpose_nonsing_inv ] ; abel_nf

end CompletingSquare

/-! ### Part 3: One-step PSD preservation -/

section PSDStep

variable (Q : Matrix (Fin n) (Fin n) ℝ)
variable (R : Matrix (Fin m) (Fin m) ℝ)
variable (S : Matrix (Fin n) (Fin m) ℝ)
variable (A : Matrix (Fin n) (Fin n) ℝ)
variable (B : Matrix (Fin n) (Fin m) ℝ)
variable (P_next Δ_next : Matrix (Fin n) (Fin n) ℝ)

/-- The stage cost is jointly PSD in (state, control):
    ∀ v u, v^T Q v + 2 v^T S u + u^T R u ≥ 0 -/
def StageCostPSD : Prop :=
  ∀ (v : Fin n → ℝ) (u : Fin m → ℝ),
    0 ≤ v ⬝ᵥ Q.mulVec v + 2 * (v ⬝ᵥ S.mulVec u) + u ⬝ᵥ R.mulVec u

/-- For any matrices M (n×m) and K (m×n) and vector v (n),
    v^T(MK)v + v^T(K^TM^T)v = 2 * v^T M (Kv).
    This holds because v^TMKv is a scalar equal to its transpose v^TK^TM^Tv. -/
lemma quadForm_cross_double (M : Matrix (Fin n) (Fin m) ℝ)
    (K : Matrix (Fin m) (Fin n) ℝ) (v : Fin n → ℝ) :
    v ⬝ᵥ (M * K).mulVec v + v ⬝ᵥ (Kᵀ * Mᵀ).mulVec v =
      2 * (v ⬝ᵥ M.mulVec (K.mulVec v)) := by
  simp +decide [ Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_mulVec, two_mul ];
  simp +decide only [dotProduct_comm];
  simp +decide [ ← Matrix.mul_assoc, ← Matrix.transpose_mul ];
  simp +decide [ Matrix.vecMul, dotProduct ];
  simp +decide only [Finset.mul_sum _ _ _];
  exact Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring )

/-- The quadratic form of the Riccati step decomposes as stage cost + W-term.
    Uses the completing-the-square identity. -/
theorem riccati_quadForm_decomp
    (W : Matrix (Fin n) (Fin n) ℝ)
    (hWs : W.IsSymm) (hGu : IsUnit (riccatiG R B W))
    (v : Fin n → ℝ) :
    let H := riccatiH S A B W
    let K := riccatiK (riccatiG R B W) H
    let u := K.mulVec v
    v ⬝ᵥ (riccatiPstep Q A W H K).mulVec v =
      (v ⬝ᵥ Q.mulVec v + 2 * (v ⬝ᵥ S.mulVec u) + u ⬝ᵥ R.mulVec u) +
      (A.mulVec v + B.mulVec u) ⬝ᵥ W.mulVec (A.mulVec v + B.mulVec u) := by
  have := @riccati_completing_square;
  simp_all +decide [ Matrix.mulVec_add, Matrix.add_mulVec, dotProduct_add ];
  have := @quadForm_cross_double;
  simp_all +decide [ Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, Matrix.dotProduct_mulVec, Matrix.vecMul_mulVec ];
  simp_all +decide [ Matrix.vecMul_add, Matrix.add_mulVec, dotProduct_add ];
  linarith [ this S ( riccatiK ( riccatiG R B W ) ( riccatiH S A B W ) ) v ]

/-
The P_new matrix from the Riccati step is symmetric.
    P = Q + Aᵀ*W*A + Hᵀ*K. Taking transpose: Pᵀ = Q + Aᵀ*W*A + Kᵀ*H.
    So P symmetric iff Hᵀ*K = Kᵀ*H. Since K = -G⁻¹H,
    Hᵀ*K = -Hᵀ*G⁻¹*H and Kᵀ*H = -Hᵀ*(G⁻¹)ᵀ*H = -Hᵀ*G⁻¹*H when G is symmetric.
    G = R + Bᵀ*W*B is symmetric since R and W are symmetric.
-/
theorem riccatiPstep_isSymm
    (hQ : Q.IsSymm) (hR : R.IsSymm) (W : Matrix (Fin n) (Fin n) ℝ)
    (hWs : W.IsSymm) (_hGu : IsUnit (riccatiG R B W)) :
    let H := riccatiH S A B W
    let K := riccatiK (riccatiG R B W) H
    (riccatiPstep Q A W H K).IsSymm := by
  unfold riccatiPstep riccatiH riccatiK;
  simp +decide [ Matrix.IsSymm, Matrix.IsSymm ] at *;
  rw [ Matrix.transpose_nonsing_inv ];
  unfold riccatiG; simp +decide [ Matrix.mul_assoc, hQ, hR, hWs ] ;

/-- Main one-step PSD preservation theorem:
    If P_{k+1} and Δ_{k+1} are PSD, and the stage cost is jointly PSD,
    then P_k (computed by the Riccati backward step) is PSD.

    Proof: By the completing-the-square identity,
    v^T P_k v = (v^T Q v + 2 v^T S(Kv) + (Kv)^T R(Kv)) + (Av + BKv)^T W (Av + BKv).
    The first term ≥ 0 by the stage cost PSD assumption.
    The second term ≥ 0 since W is PSD (proved from P_{k+1}, Δ_{k+1} PSD). -/
theorem riccati_step_posSemidef
    (hP : P_next.PosSemidef) (hΔ : Δ_next.PosSemidef)
    (hQ : Q.IsSymm) (hR : R.IsSymm)
    (hStagePSD : StageCostPSD Q R S)
    (hInv1 : IsUnit (1 + Δ_next * P_next))
    (hInv2 : IsUnit (1 + P_next * Δ_next))
    (hGu : IsUnit (riccatiG R B (riccatiW P_next Δ_next))) :
    let W := riccatiW P_next Δ_next
    let H := riccatiH S A B W
    let K := riccatiK (riccatiG R B W) H
    (riccatiPstep Q A W H K).PosSemidef := by
  intro W H K
  have hWs := riccatiW_isSymm P_next Δ_next (psd_isSymm hP) (psd_isSymm hΔ) hInv1 hInv2
  have hWpsd := riccatiW_posSemidef P_next Δ_next hP hΔ hInv1 hInv2
  apply posSemidef_of_symm_nonneg
  · exact riccatiPstep_isSymm Q R S A B hQ hR W hWs hGu
  · intro v
    rw [riccati_quadForm_decomp Q R S A B W hWs hGu v]
    exact add_nonneg (hStagePSD v _) (psd_dotProduct_nonneg hWpsd _)

end PSDStep

/-! ### Part 4: Full backward Riccati recursion -/

section FullRecursion

/-- Problem data for a single LQR stage -/
structure LQRStage (n m : ℕ) where
  Q : Matrix (Fin n) (Fin n) ℝ
  R : Matrix (Fin m) (Fin m) ℝ
  S : Matrix (Fin n) (Fin m) ℝ
  A : Matrix (Fin n) (Fin n) ℝ
  B : Matrix (Fin n) (Fin m) ℝ
  Δ_next : Matrix (Fin n) (Fin n) ℝ

/-- The backward Riccati recursion, computing P_k for k = N, N-1, ..., 0.
    `riccatiBackward stages QN i` = P_{N-i} (i steps from the end).
    - i = 0: P_N = QN (terminal cost)
    - i+1: one Riccati backward step from P_{N-i} -/
noncomputable def riccatiBackward (stages : Fin N → LQRStage n m)
    (QN : Matrix (Fin n) (Fin n) ℝ) : ℕ → Matrix (Fin n) (Fin n) ℝ
  | 0 => QN
  | i + 1 =>
    if h : i < N then
      let stage := stages ⟨N - 1 - i, by omega⟩
      let P_prev := riccatiBackward stages QN i
      let W := riccatiW P_prev stage.Δ_next
      let G := riccatiG stage.R stage.B W
      let H := riccatiH stage.S stage.A stage.B W
      let K := riccatiK G H
      riccatiPstep stage.Q stage.A W H K
    else riccatiBackward stages QN i

/-- Assumptions needed at each stage for PSD preservation -/
structure LQRStageValid (stage : LQRStage n m) (P_prev : Matrix (Fin n) (Fin n) ℝ) : Prop where
  stagePSD : StageCostPSD stage.Q stage.R stage.S
  Q_symm : stage.Q.IsSymm
  R_symm : stage.R.IsSymm
  Δ_psd : stage.Δ_next.PosSemidef
  inv1 : IsUnit (1 + stage.Δ_next * P_prev)
  inv2 : IsUnit (1 + P_prev * stage.Δ_next)
  G_inv : IsUnit (riccatiG stage.R stage.B (riccatiW P_prev stage.Δ_next))

/-- Main induction theorem: the backward Riccati recursion preserves PSD. -/
theorem riccati_backward_posSemidef
    (stages : Fin N → LQRStage n m) (QN : Matrix (Fin n) (Fin n) ℝ)
    (hQN : QN.PosSemidef)
    (hValid : ∀ (i : ℕ) (hi : i < N),
      LQRStageValid (stages ⟨N - 1 - i, by omega⟩) (riccatiBackward stages QN i)) :
    ∀ i, i ≤ N → (riccatiBackward stages QN i).PosSemidef := by
  intro i hi
  induction i with
  | zero => exact hQN
  | succ k ih =>
    simp only [riccatiBackward]
    have hk : k < N := by omega
    simp [hk]
    have hPrev := ih (by omega)
    have hStage := hValid k hk
    exact riccati_step_posSemidef
      (stages ⟨N - 1 - k, by omega⟩).Q
      (stages ⟨N - 1 - k, by omega⟩).R
      (stages ⟨N - 1 - k, by omega⟩).S
      (stages ⟨N - 1 - k, by omega⟩).A
      (stages ⟨N - 1 - k, by omega⟩).B
      (riccatiBackward stages QN k)
      (stages ⟨N - 1 - k, by omega⟩).Δ_next
      hPrev hStage.Δ_psd hStage.Q_symm hStage.R_symm hStage.stagePSD
      hStage.inv1 hStage.inv2 hStage.G_inv

end FullRecursion
-- ═══════════════════════════════════════════════════════════════════════════
-- § 3. Cost-to-Go Correctness (Theorem 3)
-- ═══════════════════════════════════════════════════════════════════════════

/-
═══════════════════════════════════════════════════════════════════════════
§ 1. Generic Completing the Square
═══════════════════════════════════════════════════════════════════════════

Generic completing the square for a quadratic function:
    If H is symmetric and H a + h = 0 (gradient vanishes at a), then
    ½ xᵀHx + hᵀx = ½(x-a)ᵀH(x-a) + (½ aᵀHa + hᵀa)

    Equivalently: f(x) = f(a) + ½(x-a)ᵀH(x-a).
-/
theorem completing_the_square_generic
    {k : ℕ} (H : Matrix (Fin k) (Fin k) ℝ) (h a x : Fin k → ℝ)
    (hH : H.IsSymm)
    (hgrad : H.mulVec a + h = 0) :
    (1/2 : ℝ) * (x ⬝ᵥ H.mulVec x) + h ⬝ᵥ x =
    (1/2 : ℝ) * ((x - a) ⬝ᵥ H.mulVec (x - a))
    + ((1/2 : ℝ) * (a ⬝ᵥ H.mulVec a) + h ⬝ᵥ a) := by
  simp_all +decide [ mul_assoc, mul_comm, mul_left_comm, sub_mul, mul_sub, Matrix.mulVec_sub, Matrix.mulVec_smul, Finset.sum_add_distrib, add_mul, mul_add, sub_eq_add_neg, add_assoc ];
  simp_all +decide [ mul_add, add_eq_zero_iff_eq_neg, dotProduct_add, dotProduct_neg, Matrix.mulVec_add, Matrix.mulVec_neg ] ; ring;
  rw [ show H *ᵥ x = H.transpose *ᵥ x from by rw [ hH ] ] ; norm_num [ Matrix.dotProduct_mulVec, Matrix.vecMul_transpose ] ; ring;
  rw [ hgrad ] ; norm_num [ dotProduct_neg, dotProduct_comm ] ; ring;

/-
Corollary: f(x) - f(a) = ½(x-a)ᵀH(x-a) when H is symmetric and ∇f(a) = 0.
-/
theorem completing_the_square_diff
    {k : ℕ} (H : Matrix (Fin k) (Fin k) ℝ) (h a x : Fin k → ℝ)
    (hH : H.IsSymm)
    (hgrad : H.mulVec a + h = 0) :
    ((1/2 : ℝ) * (x ⬝ᵥ H.mulVec x) + h ⬝ᵥ x) -
    ((1/2 : ℝ) * (a ⬝ᵥ H.mulVec a) + h ⬝ᵥ a) =
    (1/2 : ℝ) * ((x - a) ⬝ᵥ H.mulVec (x - a)) := by
  convert congr_arg ( fun y => y - ( 1 / 2 * a ⬝ᵥ H *ᵥ a + h ⬝ᵥ a ) ) ( completing_the_square_generic H h a x hH hgrad ) using 1 ; ring

-- ═══════════════════════════════════════════════════════════════════════════
-- § 2. One-Step Lagrangian
-- ═══════════════════════════════════════════════════════════════════════════

/-- The one-step Lagrangian at stage k, given V_{k+1} as a quadratic.

    L(x, u, x', y) = ½ xᵀQx + xᵀMu + ½ uᵀRu + qᵀx + rᵀu
                    + ½ x'ᵀP'x' + p'ᵀx' + const'
                    + yᵀ(Ax + Bu + c - x')
                    - ½ yᵀΔy

    where (Q, R, M, A, B, Δ, q, r, c) are the stage data and
    (P', p', const') represent V_{k+1}(x') = ½ x'ᵀP'x' + p'ᵀx' + const'. -/
noncomputable def oneStepLag
    (Q : Matrix (Fin n) (Fin n) ℝ) (R : Matrix (Fin m) (Fin m) ℝ)
    (M : Matrix (Fin n) (Fin m) ℝ) (A : Matrix (Fin n) (Fin n) ℝ)
    (B : Matrix (Fin n) (Fin m) ℝ) (Δ : Matrix (Fin n) (Fin n) ℝ)
    (q : Fin n → ℝ) (r : Fin m → ℝ) (cvec : Fin n → ℝ)
    (P' : Matrix (Fin n) (Fin n) ℝ) (p' : Fin n → ℝ) (const' : ℝ)
    (x : Fin n → ℝ) (u : Fin m → ℝ) (x' : Fin n → ℝ) (y : Fin n → ℝ) : ℝ :=
  -- Stage cost
  (1/2 : ℝ) * (x ⬝ᵥ Q.mulVec x) + x ⬝ᵥ M.mulVec u
  + (1/2 : ℝ) * (u ⬝ᵥ R.mulVec u) + q ⬝ᵥ x + r ⬝ᵥ u
  -- Next-stage value function V_{k+1}(x')
  + (1/2 : ℝ) * (x' ⬝ᵥ P'.mulVec x') + p' ⬝ᵥ x' + const'
  -- Constraint term yᵀ(Ax + Bu + c - x')
  + y ⬝ᵥ (A.mulVec x + B.mulVec u + cvec - x')
  -- Dual regularization -½ yᵀΔy
  - (1/2 : ℝ) * (y ⬝ᵥ Δ.mulVec y)

-- ═══════════════════════════════════════════════════════════════════════════
-- § 3. Optimal Values
-- ═══════════════════════════════════════════════════════════════════════════

/-- The optimal control u* = K x + k, where K = -G⁻¹H and k = -G⁻¹h.
    Here W, G, H, g, h, K, k are the standard Riccati intermediate quantities. -/
noncomputable def optU
    (R : Matrix (Fin m) (Fin m) ℝ) (M : Matrix (Fin n) (Fin m) ℝ)
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (Δ : Matrix (Fin n) (Fin n) ℝ)
    (r : Fin m → ℝ) (cvec : Fin n → ℝ)
    (P' : Matrix (Fin n) (Fin n) ℝ) (p' : Fin n → ℝ)
    (x : Fin n → ℝ) : Fin m → ℝ :=
  let W := riccatiW P' Δ
  let ψ := ((1 + P' * Δ)⁻¹).mulVec p'
  let g := ψ + W.mulVec cvec
  let G := riccatiG R B W
  let H := riccatiH M A B W
  let hvec := r + Bᵀ.mulVec g
  let K := riccatiK G H
  let kvec := -(G⁻¹).mulVec hvec
  K.mulVec x + kvec

/-- The optimal next state x'* = (I + ΔP')⁻¹(Ax + Bu* + c - Δp'). -/
noncomputable def optXNext
    (R : Matrix (Fin m) (Fin m) ℝ) (M : Matrix (Fin n) (Fin m) ℝ)
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (Δ : Matrix (Fin n) (Fin n) ℝ)
    (r : Fin m → ℝ) (cvec : Fin n → ℝ)
    (P' : Matrix (Fin n) (Fin n) ℝ) (p' : Fin n → ℝ)
    (x : Fin n → ℝ) : Fin n → ℝ :=
  let ustar := optU R M A B Δ r cvec P' p' x
  ((1 + Δ * P')⁻¹).mulVec (A.mulVec x + B.mulVec ustar + cvec - Δ.mulVec p')

/-- The optimal dual variable y* = P' x'* + p'. -/
noncomputable def optY
    (R : Matrix (Fin m) (Fin m) ℝ) (M : Matrix (Fin n) (Fin m) ℝ)
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (Δ : Matrix (Fin n) (Fin n) ℝ)
    (r : Fin m → ℝ) (cvec : Fin n → ℝ)
    (P' : Matrix (Fin n) (Fin n) ℝ) (p' : Fin n → ℝ)
    (x : Fin n → ℝ) : Fin n → ℝ :=
  let xnext := optXNext R M A B Δ r cvec P' p' x
  P'.mulVec xnext + p'

-- ═══════════════════════════════════════════════════════════════════════════
-- § 4. Gradient Conditions (First-Order Optimality)
-- ═══════════════════════════════════════════════════════════════════════════

/-- Gradient condition for x': ∂L/∂x' = P'x'* + p' - y* = 0.
    This holds by definition since y* = P'x'* + p'. -/
theorem grad_xnext_vanishes
    (R : Matrix (Fin m) (Fin m) ℝ) (M : Matrix (Fin n) (Fin m) ℝ)
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (Δ : Matrix (Fin n) (Fin n) ℝ)
    (r : Fin m → ℝ) (cvec : Fin n → ℝ)
    (P' : Matrix (Fin n) (Fin n) ℝ) (p' : Fin n → ℝ)
    (x : Fin n → ℝ) :
    let x'star := optXNext R M A B Δ r cvec P' p' x
    let ystar := optY R M A B Δ r cvec P' p' x
    P'.mulVec x'star + p' = ystar := by
  simp [optY]

/-
Gradient condition for y: ∂L/∂y = Ax + Bu* + c - x'* - Δy* = 0.
    This means: Ax + Bu* + c - x'* = Δy* = Δ(P'x'* + p').
    Equivalently: (I + ΔP')x'* = Ax + Bu* + c - Δp'.
-/
theorem grad_y_vanishes
    (R : Matrix (Fin m) (Fin m) ℝ) (M : Matrix (Fin n) (Fin m) ℝ)
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (Δ : Matrix (Fin n) (Fin n) ℝ)
    (r : Fin m → ℝ) (cvec : Fin n → ℝ)
    (P' : Matrix (Fin n) (Fin n) ℝ) (p' : Fin n → ℝ)
    (x : Fin n → ℝ)
    (hInv : IsUnit (1 + Δ * P')) :
    let ustar := optU R M A B Δ r cvec P' p' x
    let x'star := optXNext R M A B Δ r cvec P' p' x
    let ystar := optY R M A B Δ r cvec P' p' x
    A.mulVec x + B.mulVec ustar + cvec - x'star = Δ.mulVec ystar := by
  simp +decide [ optXNext, optY ];
  have h_inv : (1 + Δ * P') * (1 + Δ * P')⁻¹ = 1 := by
    exact Matrix.mul_nonsing_inv _ ( show IsUnit ( 1 + Δ * P' |> Matrix.det ) from hInv.map ( Matrix.detMonoidHom ) );
  simp_all +decide [ mul_add, add_mul, mul_assoc, Matrix.mulVec_add, Matrix.mulVec_mulVec ];
  rw [ ← eq_sub_iff_add_eq' ] at h_inv;
  simp +decide [ h_inv, Matrix.sub_mulVec ];
  abel1

/-
Gradient condition for u: ∂L/∂u = Ru* + Mᵀx + r + Bᵀy* = 0.
    This is the most complex gradient condition, requiring algebraic manipulation
    of the Riccati formulas.
-/
theorem grad_u_vanishes
    (R : Matrix (Fin m) (Fin m) ℝ) (M : Matrix (Fin n) (Fin m) ℝ)
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (Δ : Matrix (Fin n) (Fin n) ℝ)
    (r : Fin m → ℝ) (cvec : Fin n → ℝ)
    (P' : Matrix (Fin n) (Fin n) ℝ) (p' : Fin n → ℝ)
    (x : Fin n → ℝ)
    (hP's : P'.IsSymm) (hΔs : Δ.IsSymm)
    (hInv1 : IsUnit (1 + Δ * P'))
    (hInv2 : IsUnit (1 + P' * Δ))
    (hGu : IsUnit (riccatiG R B (riccatiW P' Δ))) :
    let ustar := optU R M A B Δ r cvec P' p' x
    let ystar := optY R M A B Δ r cvec P' p' x
    R.mulVec ustar + Mᵀ.mulVec x + r + Bᵀ.mulVec ystar = 0 := by
  have hG : riccatiG R B (riccatiW P' Δ) * (riccatiG R B (riccatiW P' Δ))⁻¹ = 1 := by
    exact Matrix.mul_nonsing_inv _ ( show IsUnit _ from by simpa [ Matrix.isUnit_iff_isUnit_det ] using hGu );
  have hB_y : let ustar := optU R M A B Δ r cvec P' p' x; let x'star := optXNext R M A B Δ r cvec P' p' x; let ystar := optY R M A B Δ r cvec P' p' x; Bᵀ.mulVec ystar = Bᵀ.mulVec (riccatiW P' Δ *ᵥ (A.mulVec x + B.mulVec ustar + cvec)) + Bᵀ.mulVec (((1 + P' * Δ)⁻¹).mulVec p') := by
    have hB_y : let ustar := optU R M A B Δ r cvec P' p' x; let x'star := optXNext R M A B Δ r cvec P' p' x; let ystar := optY R M A B Δ r cvec P' p' x; ystar = riccatiW P' Δ *ᵥ (A.mulVec x + B.mulVec ustar + cvec) + ((1 + P' * Δ)⁻¹).mulVec p' := by
      simp +decide [ optY, optXNext, riccatiW ];
      rw [ Matrix.mulVec_sub, ← one_sub_riccatiW_mul P' Δ hInv1 hInv2 ];
      simp +decide [ sub_mul, Matrix.sub_mulVec ];
      exact?;
    simp +decide only [hB_y, mulVec_add];
  simp_all +decide [ optU, optXNext, optY, riccatiW, riccatiG, riccatiH, riccatiK ];
  simp_all +decide [ Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, Matrix.mulVec_add, Matrix.mulVec_mulVec ];
  simp_all +decide [ ← Matrix.mul_assoc, ← eq_sub_iff_add_eq' ];
  simp_all +decide [ Matrix.add_mulVec, Matrix.mulVec_add, Matrix.mulVec_neg, Matrix.neg_mulVec, sub_eq_add_neg ];
  simp_all +decide [ ← Matrix.mul_assoc, ← Matrix.add_mulVec, ← Matrix.mulVec_add, ← Matrix.neg_mulVec, ← Matrix.mulVec_neg ];
  simp_all +decide [ Matrix.add_mulVec, Matrix.mulVec_add, Matrix.mulVec_neg, Matrix.neg_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, Matrix.mulVec_mulVec, Matrix.mulVec_add, Matrix.mulVec_neg, Matrix.neg_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.mulVec_mulVec, Matrix.mulVec_add, Matrix.mulVec_neg, Matrix.neg_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.mulVec_mulVec, Matrix.mulVec_add, Matrix.mulVec_neg, Matrix.neg_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.mulVec_mulVec ];
  abel1

/-
═══════════════════════════════════════════════════════════════════════════
§ 5. Completing the Square ⟹ Saddle-Point Conditions
═══════════════════════════════════════════════════════════════════════════

Primal completing the square: for all u and x',
    L(x, u, x', y*) = L(x, u*, x'*, y*) + ½(u-u*)ᵀR(u-u*) + ½(x'-x'*)ᵀP'(x'-x'*).

    Since R is PD (hence PSD) and P' is PSD, both extra terms are ≥ 0,
    proving that (u*, x'*) minimizes L for fixed y = y*.
-/
theorem primal_completing_square
    (Q : Matrix (Fin n) (Fin n) ℝ) (R : Matrix (Fin m) (Fin m) ℝ)
    (M : Matrix (Fin n) (Fin m) ℝ) (A : Matrix (Fin n) (Fin n) ℝ)
    (B : Matrix (Fin n) (Fin m) ℝ) (Δ : Matrix (Fin n) (Fin n) ℝ)
    (q : Fin n → ℝ) (r : Fin m → ℝ) (cvec : Fin n → ℝ)
    (P' : Matrix (Fin n) (Fin n) ℝ) (p' : Fin n → ℝ) (const' : ℝ)
    (x : Fin n → ℝ) (u : Fin m → ℝ) (x' : Fin n → ℝ)
    (hRs : R.IsSymm) (hP's : P'.IsSymm) (hΔs : Δ.IsSymm)
    (hInv1 : IsUnit (1 + Δ * P'))
    (hInv2 : IsUnit (1 + P' * Δ))
    (hGu : IsUnit (riccatiG R B (riccatiW P' Δ))) :
    let ustar := optU R M A B Δ r cvec P' p' x
    let x'star := optXNext R M A B Δ r cvec P' p' x
    let ystar := optY R M A B Δ r cvec P' p' x
    oneStepLag Q R M A B Δ q r cvec P' p' const' x u x' ystar =
    oneStepLag Q R M A B Δ q r cvec P' p' const' x ustar x'star ystar
    + (1/2 : ℝ) * ((u - ustar) ⬝ᵥ R.mulVec (u - ustar))
    + (1/2 : ℝ) * ((x' - x'star) ⬝ᵥ P'.mulVec (x' - x'star)) := by
  unfold oneStepLag;
  have h_grad_u : R.mulVec (optU R M A B Δ r cvec P' p' x) + (Mᵀ.mulVec x + r + Bᵀ.mulVec (optY R M A B Δ r cvec P' p' x)) = 0 := by
    convert grad_u_vanishes R M A B Δ r cvec P' p' x hP's hΔs hInv1 hInv2 hGu using 1;
    abel1;
  have h_grad_xnext : P'.mulVec (optXNext R M A B Δ r cvec P' p' x) + p' - optY R M A B Δ r cvec P' p' x = 0 := by
    unfold optY; aesop;
  have := completing_the_square_diff R ( Mᵀ.mulVec x + r + Bᵀ.mulVec ( optY R M A B Δ r cvec P' p' x ) ) ( optU R M A B Δ r cvec P' p' x ) u hRs h_grad_u;
  have := completing_the_square_diff P' ( p' - optY R M A B Δ r cvec P' p' x ) ( optXNext R M A B Δ r cvec P' p' x ) x' hP's ( by
    simpa only [ add_sub, sub_eq_zero ] using h_grad_xnext );
  norm_num [ Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, dotProduct_comm ] at *;
  linarith

/-
Dual completing the square: for all y,
    L(x, u*, x'*, y) = L(x, u*, x'*, y*) - ½(y-y*)ᵀΔ(y-y*).

    Since Δ is PD (hence PSD), the extra term is ≤ 0,
    proving that y* maximizes L for fixed (u*, x'*).
-/
theorem dual_completing_square
    (Q : Matrix (Fin n) (Fin n) ℝ) (R : Matrix (Fin m) (Fin m) ℝ)
    (M : Matrix (Fin n) (Fin m) ℝ) (A : Matrix (Fin n) (Fin n) ℝ)
    (B : Matrix (Fin n) (Fin m) ℝ) (Δ : Matrix (Fin n) (Fin n) ℝ)
    (q : Fin n → ℝ) (r : Fin m → ℝ) (cvec : Fin n → ℝ)
    (P' : Matrix (Fin n) (Fin n) ℝ) (p' : Fin n → ℝ) (const' : ℝ)
    (x : Fin n → ℝ) (y : Fin n → ℝ)
    (hΔs : Δ.IsSymm)
    (hP's : P'.IsSymm)
    (hInv1 : IsUnit (1 + Δ * P'))
    (hInv2 : IsUnit (1 + P' * Δ))
    (hGu : IsUnit (riccatiG R B (riccatiW P' Δ))) :
    let ustar := optU R M A B Δ r cvec P' p' x
    let x'star := optXNext R M A B Δ r cvec P' p' x
    let ystar := optY R M A B Δ r cvec P' p' x
    oneStepLag Q R M A B Δ q r cvec P' p' const' x ustar x'star y =
    oneStepLag Q R M A B Δ q r cvec P' p' const' x ustar x'star ystar
    - (1/2 : ℝ) * ((y - ystar) ⬝ᵥ Δ.mulVec (y - ystar)) := by
  unfold oneStepLag;
  have := grad_y_vanishes R M A B Δ r cvec P' p' x hInv1;
  simp_all +decide [ mul_sub, sub_mul, dotProduct_sub, sub_dotProduct ];
  simp +decide [ Matrix.mulVec_sub, dotProduct_sub ];
  rw [ show Δ *ᵥ y = Δ.transpose *ᵥ y by rw [ hΔs ] ] ; norm_num [ Matrix.dotProduct_mulVec, Matrix.vecMul_transpose ] ; ring;
  simp +decide [ Matrix.vecMul_mulVec, Matrix.dotProduct_mulVec, dotProduct_comm ] ; ring

-- ═══════════════════════════════════════════════════════════════════════════
-- § 6. Value Identity
-- ═══════════════════════════════════════════════════════════════════════════

/-- The Riccati cost-to-go value function at stage k:
    V_k(x) = ½ xᵀ P_k x + p_kᵀ x + const_k -/
noncomputable def riccatiValue
    (Q : Matrix (Fin n) (Fin n) ℝ) (R : Matrix (Fin m) (Fin m) ℝ)
    (M : Matrix (Fin n) (Fin m) ℝ) (A : Matrix (Fin n) (Fin n) ℝ)
    (B : Matrix (Fin n) (Fin m) ℝ) (Δ : Matrix (Fin n) (Fin n) ℝ)
    (q : Fin n → ℝ) (r : Fin m → ℝ) (cvec : Fin n → ℝ)
    (P' : Matrix (Fin n) (Fin n) ℝ) (p' : Fin n → ℝ) (const' : ℝ)
    (x : Fin n → ℝ) : ℝ :=
  let W := riccatiW P' Δ
  let ψ := ((1 + P' * Δ)⁻¹).mulVec p'
  let g := ψ + W.mulVec cvec
  let G := riccatiG R B W
  let H := riccatiH M A B W
  let hvec := r + Bᵀ.mulVec g
  let K := riccatiK G H
  let kvec := -(G⁻¹).mulVec hvec
  let Pk := riccatiPstep Q A W H K
  let pk := q + Aᵀ.mulVec g + Hᵀ.mulVec kvec
  let constk := const'
    + (1/2 : ℝ) * (cvec ⬝ᵥ W.mulVec cvec)
    + ψ ⬝ᵥ cvec
    - (1/2 : ℝ) * (ψ ⬝ᵥ Δ.mulVec p')
    + (1/2 : ℝ) * (hvec ⬝ᵥ kvec)
  (1/2 : ℝ) * (x ⬝ᵥ Pk.mulVec x) + pk ⬝ᵥ x + constk

/-
Step 1 of value identity: The Lagrangian at the saddle point simplifies
    using the gradient conditions to: stage cost + V_{k+1}(x'*) + ½ y*ᵀΔy*.
-/
theorem value_identity_step1
    (Q : Matrix (Fin n) (Fin n) ℝ) (R : Matrix (Fin m) (Fin m) ℝ)
    (M : Matrix (Fin n) (Fin m) ℝ) (A : Matrix (Fin n) (Fin n) ℝ)
    (B : Matrix (Fin n) (Fin m) ℝ) (Δ : Matrix (Fin n) (Fin n) ℝ)
    (q : Fin n → ℝ) (r : Fin m → ℝ) (cvec : Fin n → ℝ)
    (P' : Matrix (Fin n) (Fin n) ℝ) (p' : Fin n → ℝ) (const' : ℝ)
    (x : Fin n → ℝ)
    (hΔs : Δ.IsSymm) (hP's : P'.IsSymm)
    (hInv1 : IsUnit (1 + Δ * P'))
    (hInv2 : IsUnit (1 + P' * Δ))
    (hGu : IsUnit (riccatiG R B (riccatiW P' Δ))) :
    let ustar := optU R M A B Δ r cvec P' p' x
    let x'star := optXNext R M A B Δ r cvec P' p' x
    let ystar := optY R M A B Δ r cvec P' p' x
    oneStepLag Q R M A B Δ q r cvec P' p' const' x ustar x'star ystar =
    oneStepLag Q R M A B Δ q r cvec P' p' const' x ustar x'star 0
    + (1/2 : ℝ) * (ystar ⬝ᵥ Δ.mulVec ystar) := by
  have h := dual_completing_square Q R M A B Δ q r cvec P' p' const' x 0 hΔs hP's hInv1 hInv2 hGu;
  convert eq_add_of_sub_eq' h.symm using 1 ; norm_num [ dotProduct, Matrix.mulVec ] ; ring!;

-- ═══════════════════════════════════════════════════════════════════════════
-- § 5b. Helper lemmas for the value identity
-- ═══════════════════════════════════════════════════════════════════════════

set_option maxHeartbeats 1600000 in
theorem ystar_eq_Wv_plus_psi
    (R : Matrix (Fin m) (Fin m) ℝ) (M : Matrix (Fin n) (Fin m) ℝ)
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (Δ : Matrix (Fin n) (Fin n) ℝ)
    (r : Fin m → ℝ) (cvec : Fin n → ℝ)
    (P' : Matrix (Fin n) (Fin n) ℝ) (p' : Fin n → ℝ)
    (x : Fin n → ℝ)
    (hInv1 : IsUnit (1 + Δ * P'))
    (hInv2 : IsUnit (1 + P' * Δ)) :
    let ustar := optU R M A B Δ r cvec P' p' x
    let v := A.mulVec x + B.mulVec ustar + cvec
    let W := riccatiW P' Δ
    let ψ := ((1 + P' * Δ)⁻¹).mulVec p'
    optY R M A B Δ r cvec P' p' x = W.mulVec v + ψ := by
  simp +decide [ optY, optXNext ]
  rw [ ← one_sub_riccatiW_mul P' Δ hInv1 hInv2 ]
  rw [ Matrix.sub_mulVec, Matrix.mulVec_add, Matrix.mulVec_sub ]
  simp +decide [ Matrix.mulVec_add, Matrix.mulVec_sub, Matrix.mulVec_smul, riccatiW ] ; abel_nf

set_option maxHeartbeats 1600000 in
theorem pdot_xnext_eq
    (R : Matrix (Fin m) (Fin m) ℝ) (M : Matrix (Fin n) (Fin m) ℝ)
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (Δ : Matrix (Fin n) (Fin n) ℝ)
    (r : Fin m → ℝ) (cvec : Fin n → ℝ)
    (P' : Matrix (Fin n) (Fin n) ℝ) (p' : Fin n → ℝ)
    (x : Fin n → ℝ)
    (hP's : P'.IsSymm) (hΔs : Δ.IsSymm) :
    let ustar := optU R M A B Δ r cvec P' p' x
    let v := A.mulVec x + B.mulVec ustar + cvec
    let ψ := ((1 + P' * Δ)⁻¹).mulVec p'
    p' ⬝ᵥ (optXNext R M A B Δ r cvec P' p' x) = ψ ⬝ᵥ (v - Δ.mulVec p') := by
  unfold optXNext
  simp +decide [ Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_mulVec, Matrix.transpose_nonsing_inv, hP's.eq, hΔs.eq ]
  rw [ ← Matrix.mulVec_transpose, Matrix.transpose_nonsing_inv, Matrix.transpose_add, Matrix.transpose_mul, hP's.eq, hΔs.eq ] ; norm_num [ Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_mulVec, Matrix.transpose_nonsing_inv, hP's.eq, hΔs.eq ]

set_option maxHeartbeats 1600000 in
theorem xnext_terms_simplify
    (R : Matrix (Fin m) (Fin m) ℝ) (M : Matrix (Fin n) (Fin m) ℝ)
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (Δ : Matrix (Fin n) (Fin n) ℝ)
    (r : Fin m → ℝ) (cvec : Fin n → ℝ)
    (P' : Matrix (Fin n) (Fin n) ℝ) (p' : Fin n → ℝ) (const' : ℝ)
    (x : Fin n → ℝ)
    (hP's : P'.IsSymm) (hΔs : Δ.IsSymm)
    (hInv1 : IsUnit (1 + Δ * P'))
    (hInv2 : IsUnit (1 + P' * Δ)) :
    let ustar := optU R M A B Δ r cvec P' p' x
    let x'star := optXNext R M A B Δ r cvec P' p' x
    let ystar := optY R M A B Δ r cvec P' p' x
    let v := A.mulVec x + B.mulVec ustar + cvec
    let W := riccatiW P' Δ
    let ψ := ((1 + P' * Δ)⁻¹).mulVec p'
    (1/2 : ℝ) * (x'star ⬝ᵥ P'.mulVec x'star) + p' ⬝ᵥ x'star
    + (1/2 : ℝ) * (ystar ⬝ᵥ Δ.mulVec ystar)
    = (1/2 : ℝ) * (v ⬝ᵥ W.mulVec v) + ψ ⬝ᵥ v
    - (1/2 : ℝ) * (ψ ⬝ᵥ Δ.mulVec p') := by
  -- Use the gradient condition P'.mulVec x'star + (p' - ystar) = 0 to simplify the dot products.
  have h_grad : P'.mulVec (optXNext R M A B Δ r cvec P' p' x) + (p' - optY R M A B Δ r cvec P' p' x) = 0 := by
    simp +decide [ sub_eq_iff_eq_add, optY ];
  have h_simp : let ustar := optU R M A B Δ r cvec P' p' x;
    let x'star := optXNext R M A B Δ r cvec P' p' x;
    let ystar := optY R M A B Δ r cvec P' p' x;
    let v := A.mulVec x + B.mulVec ustar + cvec;
    let W := riccatiW P' Δ;
    let ψ := ((1 + P' * Δ)⁻¹).mulVec p';
    (1/2 : ℝ) * x'star ⬝ᵥ P'.mulVec x'star + p' ⬝ᵥ x'star + (1/2 : ℝ) * ystar ⬝ᵥ Δ.mulVec ystar =
    (1/2 : ℝ) * ystar ⬝ᵥ v + (1/2 : ℝ) * p' ⬝ᵥ x'star := by
      have h_simp : let ustar := optU R M A B Δ r cvec P' p' x;
        let x'star := optXNext R M A B Δ r cvec P' p' x;
        let ystar := optY R M A B Δ r cvec P' p' x;
        let v := A.mulVec x + B.mulVec ustar + cvec;
        (1/2 : ℝ) * x'star ⬝ᵥ P'.mulVec x'star + p' ⬝ᵥ x'star + (1/2 : ℝ) * ystar ⬝ᵥ Δ.mulVec ystar =
        (1/2 : ℝ) * ystar ⬝ᵥ (x'star + Δ.mulVec ystar) + (1/2 : ℝ) * p' ⬝ᵥ x'star := by
          simp +zetaDelta at *;
          rw [ show P' *ᵥ optXNext R M A B Δ r cvec P' p' x = optY R M A B Δ r cvec P' p' x - p' by ext i; have := congr_fun h_grad i; norm_num at *; linarith ] ; norm_num [ dotProduct_comm ] ; ring;
      convert h_simp using 3;
      convert Iff.rfl using 3 ; ring;
      rw [ ← grad_y_vanishes R M A B Δ r cvec P' p' x hInv1 ] ; ring;
  convert h_simp using 1;
  rw [ ystar_eq_Wv_plus_psi _ _ _ _ _ _ _ _ _ _ hInv1 hInv2 ];
  have h_simp : let ustar := optU R M A B Δ r cvec P' p' x;
    let x'star := optXNext R M A B Δ r cvec P' p' x;
    let v := A.mulVec x + B.mulVec ustar + cvec;
    let W := riccatiW P' Δ;
    let ψ := ((1 + P' * Δ)⁻¹).mulVec p';
    p' ⬝ᵥ x'star = ψ ⬝ᵥ (v - Δ.mulVec p') := by
      exact?;
  simp_all +decide [ Matrix.dotProduct_mulVec, Matrix.vecMul_mulVec, dotProduct_comm ];
  grind

set_option maxHeartbeats 1600000 in
theorem G_grad_vanishes
    (R : Matrix (Fin m) (Fin m) ℝ) (M : Matrix (Fin n) (Fin m) ℝ)
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (Δ : Matrix (Fin n) (Fin n) ℝ)
    (r : Fin m → ℝ) (cvec : Fin n → ℝ)
    (P' : Matrix (Fin n) (Fin n) ℝ) (p' : Fin n → ℝ)
    (x : Fin n → ℝ)
    (hGu : IsUnit (riccatiG R B (riccatiW P' Δ))) :
    let W := riccatiW P' Δ
    let ψ := ((1 + P' * Δ)⁻¹).mulVec p'
    let g := ψ + W.mulVec cvec
    let G := riccatiG R B W
    let H := riccatiH M A B W
    let hvec := r + Bᵀ.mulVec g
    let ustar := optU R M A B Δ r cvec P' p' x
    G.mulVec ustar + H.mulVec x + hvec = 0 := by
  unfold optU;
  simp +decide [ Matrix.isUnit_iff_isUnit_det ] at hGu;
  unfold riccatiK;
  simp +decide [ Matrix.mulVec_add, Matrix.mulVec_neg, Matrix.neg_mulVec, hGu, isUnit_iff_ne_zero ];
  abel1

theorem riccatiG_isSymm'
    (R : Matrix (Fin m) (Fin m) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (W : Matrix (Fin n) (Fin n) ℝ)
    (hRs : R.IsSymm) (hWs : W.IsSymm) :
    (riccatiG R B W).IsSymm := by
  unfold riccatiG
  simp_all +decide [ Matrix.IsSymm, Matrix.mul_assoc ]

set_option maxHeartbeats 1600000 in
theorem ustar_quadratic_at_opt
    (R : Matrix (Fin m) (Fin m) ℝ) (M : Matrix (Fin n) (Fin m) ℝ)
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (Δ : Matrix (Fin n) (Fin n) ℝ)
    (r : Fin m → ℝ) (cvec : Fin n → ℝ)
    (P' : Matrix (Fin n) (Fin n) ℝ) (p' : Fin n → ℝ)
    (x : Fin n → ℝ)
    (hRs : R.IsSymm) (hP's : P'.IsSymm) (hΔs : Δ.IsSymm)
    (hInv1 : IsUnit (1 + Δ * P'))
    (hInv2 : IsUnit (1 + P' * Δ))
    (hGu : IsUnit (riccatiG R B (riccatiW P' Δ))) :
    let W := riccatiW P' Δ
    let ψ := ((1 + P' * Δ)⁻¹).mulVec p'
    let g := ψ + W.mulVec cvec
    let G := riccatiG R B W
    let H := riccatiH M A B W
    let hvec := r + Bᵀ.mulVec g
    let K := riccatiK G H
    let kvec := -(G⁻¹).mulVec hvec
    let ustar := optU R M A B Δ r cvec P' p' x
    (1/2 : ℝ) * (ustar ⬝ᵥ G.mulVec ustar) + (H.mulVec x + hvec) ⬝ᵥ ustar
    = (1/2 : ℝ) * (x ⬝ᵥ (Hᵀ * K).mulVec x) + (Hᵀ.mulVec kvec) ⬝ᵥ x
    + (1/2 : ℝ) * (hvec ⬝ᵥ kvec) := by
  unfold optU
  simp +decide [ Matrix.mulVec_add, Matrix.mulVec_neg, Matrix.mulVec_smul, dotProduct_add, dotProduct_smul, dotProduct_comm ]
  unfold riccatiK
  simp +decide [ ← Matrix.mul_assoc, ← Matrix.dotProduct_mulVec, ← Matrix.vecMul_mulVec, dotProduct_comm ]
  rw [ Matrix.mul_nonsing_inv _ ]
  · simp +decide [ Matrix.mul_assoc, Matrix.dotProduct_mulVec, Matrix.vecMul_mulVec, dotProduct_comm ]
    rw [ Matrix.transpose_nonsing_inv ]
    rw [ show ( riccatiG R B ( riccatiW P' Δ ) )ᵀ = riccatiG R B ( riccatiW P' Δ ) from ?_ ]
    · norm_num [ Matrix.vecMul_neg, dotProduct_neg ] ; ring
    · apply riccatiG_isSymm'; assumption; exact riccatiW_isSymm P' Δ hP's hΔs hInv1 hInv2
  · exact IsUnit.map ( Matrix.detMonoidHom ) hGu

/-
Expansion of ½(a+b+c)ᵀW(a+b+c) into quadratic, cross, and constant terms.
-/
theorem half_trilinear_expand
    {k : ℕ} (W : Matrix (Fin k) (Fin k) ℝ)
    (a b c : Fin k → ℝ) (hWs : W.IsSymm) :
    (1/2 : ℝ) * ((a + b + c) ⬝ᵥ W.mulVec (a + b + c)) =
    (1/2 : ℝ) * (a ⬝ᵥ W.mulVec a) + a ⬝ᵥ W.mulVec b + a ⬝ᵥ W.mulVec c
    + (1/2 : ℝ) * (b ⬝ᵥ W.mulVec b) + b ⬝ᵥ W.mulVec c
    + (1/2 : ℝ) * (c ⬝ᵥ W.mulVec c) := by
  simp +decide [ Matrix.mulVec, dotProduct ] ; ring!;
  simp +decide [ Matrix.vecMul, dotProduct, Finset.sum_add_distrib, add_mul, mul_add, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _, Finset.sum_mul ] ; ring!;
  simp +decide [ ← Finset.mul_sum _ _ _, ← Finset.sum_mul, ← Finset.sum_comm, hWs.apply ] ; ring!;

/-
Bilinear expansion of v = Ax + Bu + c in ½vᵀWv + ψᵀv, combined with stage cost.
-/
theorem expand_v_bilinear
    (Q : Matrix (Fin n) (Fin n) ℝ) (R : Matrix (Fin m) (Fin m) ℝ)
    (M : Matrix (Fin n) (Fin m) ℝ) (A : Matrix (Fin n) (Fin n) ℝ)
    (B : Matrix (Fin n) (Fin m) ℝ)
    (W : Matrix (Fin n) (Fin n) ℝ)
    (q : Fin n → ℝ) (r : Fin m → ℝ) (cvec : Fin n → ℝ)
    (ψ : Fin n → ℝ)
    (x : Fin n → ℝ) (u : Fin m → ℝ)
    (hWs : W.IsSymm) :
    let v := A.mulVec x + B.mulVec u + cvec
    let g := ψ + W.mulVec cvec
    let G := riccatiG R B W
    let H := riccatiH M A B W
    let hvec := r + Bᵀ.mulVec g
    (1/2 : ℝ) * (x ⬝ᵥ Q.mulVec x) + x ⬝ᵥ M.mulVec u
    + (1/2 : ℝ) * (u ⬝ᵥ R.mulVec u) + q ⬝ᵥ x + r ⬝ᵥ u
    + (1/2 : ℝ) * (v ⬝ᵥ W.mulVec v) + ψ ⬝ᵥ v
    = (1/2 : ℝ) * (x ⬝ᵥ (Q + Aᵀ * W * A).mulVec x)
    + (1/2 : ℝ) * (u ⬝ᵥ G.mulVec u)
    + (H.mulVec x + hvec) ⬝ᵥ u
    + (q + Aᵀ.mulVec g) ⬝ᵥ x
    + (1/2 : ℝ) * (cvec ⬝ᵥ W.mulVec cvec) + ψ ⬝ᵥ cvec := by
  unfold riccatiG riccatiH;
  have := @half_trilinear_expand n W ( A.mulVec x ) ( B.mulVec u ) cvec hWs; simp_all +decide [ Matrix.mulVec_add, Matrix.mulVec_mulVec ] ;
  simp_all +decide [ Matrix.add_mulVec, Matrix.mulVec_add, Matrix.dotProduct_mulVec, Matrix.vecMul_mulVec, Matrix.mul_assoc, Matrix.transpose_mul, Matrix.transpose_nonsing_inv ];
  simp_all +decide [ Matrix.vecMul_mulVec, Matrix.vecMul_transpose, Matrix.dotProduct_mulVec, Matrix.mulVec_transpose, dotProduct_comm ] ; ring!;
  rw [ show x ⬝ᵥ u ᵥ* ( Bᵀ * ( W * A ) ) = u ⬝ᵥ x ᵥ* ( Aᵀ * ( W * B ) ) from ?_ ] ; ring;
  simp +decide [ Matrix.vecMul, dotProduct, Finset.mul_sum _ _ _, mul_assoc, mul_comm, mul_left_comm ];
  rw [ Finset.sum_comm ] ; congr ; ext ; congr ; ext ; simp +decide [ Matrix.mul_apply, mul_assoc, mul_comm, mul_left_comm ] ; ring;
  simp +decide only [Finset.mul_sum _ _ _, mul_left_comm];
  exact Or.inl <| Or.inl <| Finset.sum_comm.trans <| Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by rw [ hWs.apply ] ;

set_option maxHeartbeats 4000000 in
/-- Step 2 of value identity: The Lagrangian at y=0 plus the dual regularization
    term equals the Riccati value function.

    Proof strategy (following the LaTeX sequential algorithm proof):
    1. Use xnext_terms_simplify to replace the x'*/y* terms with W, ψ expressions
    2. Expand v = Ax+Bu*+c, collect u*-dependent terms
    3. Use ustar_quadratic_at_opt to simplify the u* quadratic
    4. Collect remaining terms into riccatiValue -/
theorem value_identity_step2
    (Q : Matrix (Fin n) (Fin n) ℝ) (R : Matrix (Fin m) (Fin m) ℝ)
    (M : Matrix (Fin n) (Fin m) ℝ) (A : Matrix (Fin n) (Fin n) ℝ)
    (B : Matrix (Fin n) (Fin m) ℝ) (Δ : Matrix (Fin n) (Fin n) ℝ)
    (q : Fin n → ℝ) (r : Fin m → ℝ) (cvec : Fin n → ℝ)
    (P' : Matrix (Fin n) (Fin n) ℝ) (p' : Fin n → ℝ) (const' : ℝ)
    (x : Fin n → ℝ)
    (hRs : R.IsSymm) (hP's : P'.IsSymm) (hΔs : Δ.IsSymm)
    (hInv1 : IsUnit (1 + Δ * P'))
    (hInv2 : IsUnit (1 + P' * Δ))
    (hGu : IsUnit (riccatiG R B (riccatiW P' Δ))) :
    let ustar := optU R M A B Δ r cvec P' p' x
    let x'star := optXNext R M A B Δ r cvec P' p' x
    let ystar := optY R M A B Δ r cvec P' p' x
    oneStepLag Q R M A B Δ q r cvec P' p' const' x ustar x'star 0
    + (1/2 : ℝ) * (ystar ⬝ᵥ Δ.mulVec ystar)
    = riccatiValue Q R M A B Δ q r cvec P' p' const' x := by
  unfold oneStepLag riccatiValue;
  have := xnext_terms_simplify R M A B Δ r cvec P' p' const' x hP's hΔs hInv1 hInv2;
  have := expand_v_bilinear Q R M A B (riccatiW P' Δ) q r cvec
    (((1 + P' * Δ)⁻¹).mulVec p') x (optU R M A B Δ r cvec P' p' x)
    (riccatiW_isSymm P' Δ hP's hΔs hInv1 hInv2);
  have := ustar_quadratic_at_opt R M A B Δ r cvec P' p' x hRs hP's hΔs hInv1 hInv2 hGu;
  unfold riccatiPstep; norm_num [ Matrix.add_mulVec, Matrix.mulVec_add, Matrix.mulVec_mulVec ] at * ; linarith;

/-- The value identity: L(x, u*, x'*, y*) = V_k(x).
    This shows the Lagrangian at the saddle point equals the Riccati cost-to-go. -/
theorem value_identity
    (Q : Matrix (Fin n) (Fin n) ℝ) (R : Matrix (Fin m) (Fin m) ℝ)
    (M : Matrix (Fin n) (Fin m) ℝ) (A : Matrix (Fin n) (Fin n) ℝ)
    (B : Matrix (Fin n) (Fin m) ℝ) (Δ : Matrix (Fin n) (Fin n) ℝ)
    (q : Fin n → ℝ) (r : Fin m → ℝ) (cvec : Fin n → ℝ)
    (P' : Matrix (Fin n) (Fin n) ℝ) (p' : Fin n → ℝ) (const' : ℝ)
    (x : Fin n → ℝ)
    (hRs : R.IsSymm) (hP's : P'.IsSymm) (hΔs : Δ.IsSymm)
    (hInv1 : IsUnit (1 + Δ * P'))
    (hInv2 : IsUnit (1 + P' * Δ))
    (hGu : IsUnit (riccatiG R B (riccatiW P' Δ))) :
    let ustar := optU R M A B Δ r cvec P' p' x
    let x'star := optXNext R M A B Δ r cvec P' p' x
    let ystar := optY R M A B Δ r cvec P' p' x
    oneStepLag Q R M A B Δ q r cvec P' p' const' x ustar x'star ystar =
    riccatiValue Q R M A B Δ q r cvec P' p' const' x := by
  have h1 := value_identity_step1 Q R M A B Δ q r cvec P' p' const' x hΔs hP's hInv1 hInv2 hGu
  have h2 := value_identity_step2 Q R M A B Δ q r cvec P' p' const' x hRs hP's hΔs hInv1 hInv2 hGu
  simp only at h1 h2 ⊢
  linarith

-- ═══════════════════════════════════════════════════════════════════════════
-- § 7. Main Theorem: One-Step Riccati Correctness
-- ═══════════════════════════════════════════════════════════════════════════

/-- **One-step Riccati correctness theorem:**
    The Riccati optimal (u*, x'*, y*) form a saddle point of the one-step
    Lagrangian, and the saddle-point value is the Riccati cost-to-go V_k(x).

    This proves that the backward Riccati recursion actually computes the
    cost-to-go of the dual-regularized LQR problem. -/
theorem riccati_one_step_correct
    (Q : Matrix (Fin n) (Fin n) ℝ) (R : Matrix (Fin m) (Fin m) ℝ)
    (M : Matrix (Fin n) (Fin m) ℝ) (A : Matrix (Fin n) (Fin n) ℝ)
    (B : Matrix (Fin n) (Fin m) ℝ) (Δ : Matrix (Fin n) (Fin n) ℝ)
    (q : Fin n → ℝ) (r : Fin m → ℝ) (cvec : Fin n → ℝ)
    (P' : Matrix (Fin n) (Fin n) ℝ) (p' : Fin n → ℝ) (const' : ℝ)
    (x : Fin n → ℝ)
    (hRs : R.IsSymm) (hP's : P'.IsSymm) (hΔs : Δ.IsSymm)
    (hP'psd : P'.PosSemidef) (hΔpsd : Δ.PosSemidef) (hRpsd : R.PosSemidef)
    (hInv1 : IsUnit (1 + Δ * P'))
    (hInv2 : IsUnit (1 + P' * Δ))
    (hGu : IsUnit (riccatiG R B (riccatiW P' Δ))) :
    let ustar := optU R M A B Δ r cvec P' p' x
    let x'star := optXNext R M A B Δ r cvec P' p' x
    let ystar := optY R M A B Δ r cvec P' p' x
    let Vk := riccatiValue Q R M A B Δ q r cvec P' p' const' x
    -- (1) Primal minimality: (u*, x'*) minimizes L for y = y*
    (∀ u x', oneStepLag Q R M A B Δ q r cvec P' p' const' x u x' ystar ≥ Vk)
    ∧
    -- (2) Dual maximality: y* maximizes L for (u*, x'*)
    (∀ y, oneStepLag Q R M A B Δ q r cvec P' p' const' x ustar x'star y ≤ Vk)
    ∧
    -- (3) Value identity
    (oneStepLag Q R M A B Δ q r cvec P' p' const' x ustar x'star ystar = Vk) := by
  constructor
  · -- Primal minimality
    intro u x'
    have hcs := primal_completing_square Q R M A B Δ q r cvec P' p' const' x u x'
      hRs hP's hΔs hInv1 hInv2 hGu
    have hvi := value_identity Q R M A B Δ q r cvec P' p' const' x
      hRs hP's hΔs hInv1 hInv2 hGu
    simp only at hcs hvi ⊢
    rw [hcs, hvi]
    linarith [psd_dotProduct_nonneg hRpsd (u - optU R M A B Δ r cvec P' p' x),
              psd_dotProduct_nonneg hP'psd (x' - optXNext R M A B Δ r cvec P' p' x)]
  constructor
  · -- Dual maximality
    intro y
    have hcs := dual_completing_square Q R M A B Δ q r cvec P' p' const' x y
      hΔs hP's hInv1 hInv2 hGu
    have hvi := value_identity Q R M A B Δ q r cvec P' p' const' x
      hRs hP's hΔs hInv1 hInv2 hGu
    simp only at hcs hvi ⊢
    rw [hcs, hvi]
    linarith [psd_dotProduct_nonneg hΔpsd (y - optY R M A B Δ r cvec P' p' x)]
  · -- Value identity
    exact value_identity Q R M A B Δ q r cvec P' p' const' x
      hRs hP's hΔs hInv1 hInv2 hGu
-- ═══════════════════════════════════════════════════════════════════════════
-- § 4. Alternative p-Recurrence (Corollary)
-- ═══════════════════════════════════════════════════════════════════════════

set_option linter.unusedSectionVars false

/-- Key identity: when G is symmetric and invertible, Hᵀ(G⁻¹ h) = (G⁻¹ H)ᵀ h.
    This holds because (G⁻¹)ᵀ = (Gᵀ)⁻¹ = G⁻¹ when G is symmetric. -/
theorem transpose_inv_mul_vec_comm
    (G : Matrix (Fin m) (Fin m) ℝ) (H : Matrix (Fin m) (Fin n) ℝ)
    (h : Fin m → ℝ) (hGs : G.IsSymm) (_hGu : IsUnit G) :
    (Hᵀ).mulVec (G⁻¹.mulVec h) = (G⁻¹ * H)ᵀ.mulVec h := by
  simp +decide [Matrix.mulVec_mulVec, Matrix.transpose_nonsing_inv, hGs.eq]

/-- **Corollary (p-recurrence):** The linear coefficient recursion has the
    equivalent form `q + Kᵀ r + (A + BK)ᵀ g`.

    Starting from the original form `q + Aᵀ g + Hᵀ k` where `k = -G⁻¹ h`
    and `h = r + Bᵀ g`, we show:

    `Aᵀ g + Hᵀ k = Kᵀ r + (A + BK)ᵀ g`

    The proof uses Hᵀk = Kᵀh (by G symmetric), then expands
    `Kᵀ h = Kᵀ(r + Bᵀg) = Kᵀr + (BK)ᵀg`. -/
theorem p_recurrence_corollary
    (_Q : Matrix (Fin n) (Fin n) ℝ)
    (R : Matrix (Fin m) (Fin m) ℝ)
    (S : Matrix (Fin n) (Fin m) ℝ)
    (A : Matrix (Fin n) (Fin n) ℝ)
    (B : Matrix (Fin n) (Fin m) ℝ)
    (W : Matrix (Fin n) (Fin n) ℝ)
    (q : Fin n → ℝ) (r : Fin m → ℝ) (g : Fin n → ℝ)
    (hWs : W.IsSymm) (hRs : R.IsSymm)
    (_hGu : IsUnit (riccatiG R B W)) :
    let G := riccatiG R B W
    let H := riccatiH S A B W
    let K := riccatiK G H
    let h := r + (Bᵀ).mulVec g
    let k := -(G⁻¹).mulVec h
    q + (Aᵀ).mulVec g + (Hᵀ).mulVec k =
    q + (Kᵀ).mulVec r + ((A + B * K)ᵀ).mulVec g := by
  simp [riccatiK, riccatiH, riccatiG] at *
  simp +decide [Matrix.mulVec_add, Matrix.mulVec_neg, Matrix.add_mulVec, Matrix.neg_mulVec,
    Matrix.mulVec_mulVec, Matrix.transpose_nonsing_inv]
  simp +decide [Matrix.mul_assoc, Matrix.add_mul, hWs.eq, hRs.eq]
  abel_nf
