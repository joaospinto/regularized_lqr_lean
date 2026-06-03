/-
# Parallel Riccati Recursion

This file defines and partially verifies the parallel (scan-based) algorithm
for the dual-regularized LQR backward pass.

## Definitions

1. **Interval value functions** V_{i→j}(xᵢ, xⱼ) parametrized by 5 components
   (P, p, A, C, c)
2. **Base case** (length-1 intervals) from the DualRegLQR problem data
3. **Combination rules** for composing two interval value functions

## What is proved

- Structural preservation: combining with a terminal IVF (A=C=c=0) preserves
  these zero components (`ivfCombine_Amat_zero`, `ivfCombine_C_zero`, etc.).
- Woodbury identity: `woodbury_riccati` relating parallel and sequential W.
- One-step P matching: `parallel_P_step` — the P component of one IVF
  combination step matches the sequential Riccati P update.
- One-step p matching: `parallel_p_step`.
- Schur complement identity: `schur_complement_parallel_sequential`.
- Full inductive matching: `ivfFoldRight_P_eq_backwardP` and
  `ivfFoldRight_p_eq_backwardp` — the right-fold matches sequential Riccati.
- Main theorem: `parallel_riccati_main` — bundles all results.

## Combination Rule Correctness

- `ivfCombine_gradient_vanishes` (first-order optimality)
- `ivfCombine_completing_square` (completing the square identity)
- `ivfCombine_is_minimum` (minimality corollary)

## Notes

- Base-case correctness (`ivfInitRunning_base_case_correct`): proved as an
  algebraic identity (substituting u* into the stage Lagrangian).

References:
- Combination rules from Deng & Bhatt, "Massively Parallel Computation of
  Optimal Control Solutions for LQR" (arXiv:2104.03186)
- The dual-regularized extension from Sousa-Pinto & Orban
-/
import Mathlib
import RequestProject.SequentialRiccati
import RequestProject.DualRegLQR
import RequestProject.ParallelHelpers

open Matrix

set_option maxHeartbeats 1600000

variable {n m : ℕ} [DecidableEq (Fin n)] [DecidableEq (Fin m)]

-- ═══════════════════════════════════════════════════════════════════════════
-- § 1. Interval Value Function Structure
-- ═══════════════════════════════════════════════════════════════════════════

/-- Parametrization of an interval value function V_{i→j}(xᵢ, xⱼ).

In inner form (before optimizing over the dual variable y):
```
  V_{i→j}(xᵢ, xⱼ) = max_y [ ½ xᵢᵀ P xᵢ + pᵀ xᵢ
                              - ½ yᵀ C y
                              + yᵀ (A xᵢ + c - xⱼ) ]
```

When C is positive definite, using Lemma 1 (quadratic maximization),
this evaluates to:
```
  V_{i→j}(xᵢ, xⱼ) = ½ xᵢᵀ P xᵢ + pᵀ xᵢ
                     + ½ (A xᵢ + c - xⱼ)ᵀ C⁻¹ (A xᵢ + c - xⱼ)
                     + const
```

The 5 components are:
- `P` : n×n matrix (Hessian w.r.t. left endpoint xᵢ)
- `p` : n-vector (linear term w.r.t. left endpoint xᵢ)
- `Amat` : n×n matrix (coupling left endpoint to constraint)
- `C` : n×n matrix (dual regularization/penalty)
- `cvec` : n-vector (constraint offset) -/
structure IntervalValueFn (n : ℕ) where
  P : Matrix (Fin n) (Fin n) ℝ
  p : Fin n → ℝ
  Amat : Matrix (Fin n) (Fin n) ℝ
  C : Matrix (Fin n) (Fin n) ℝ
  cvec : Fin n → ℝ

-- ═══════════════════════════════════════════════════════════════════════════
-- § 2. Base Case Definitions (Length-1 Intervals)
-- ═══════════════════════════════════════════════════════════════════════════

/-- Base case for running stages i ∈ {0, …, N−1}:

After eliminating the control variable uᵢ from the stage cost
(by setting uᵢ = −Rᵢ⁻¹(Mᵢᵀ xᵢ + rᵢ + Bᵢᵀ yᵢ₊₁)), the
length-1 interval value function V_{i→i+1} has parameters:

```
  P_{i→i+1} = Qᵢ − Mᵢ Rᵢ⁻¹ Mᵢᵀ     (Schur complement of stage cost)
  p_{i→i+1} = qᵢ − Mᵢ Rᵢ⁻¹ rᵢ       (reduced linear term)
  A_{i→i+1} = Aᵢ − Bᵢ Rᵢ⁻¹ Mᵢᵀ     (reduced dynamics)
  C_{i→i+1} = Δᵢ₊₁ + Bᵢ Rᵢ⁻¹ Bᵢᵀ   (augmented dual regularization)
  c_{i→i+1} = cᵢ₊₁ − Bᵢ Rᵢ⁻¹ rᵢ    (reduced constraint offset)
```
-/
noncomputable def ivfInitRunning {N : ℕ}
    (prob : DualRegLQR n m N) (i : Fin N) : IntervalValueFn n :=
  let Qi := prob.Q ⟨i.val, by omega⟩
  let Ri := prob.R i
  let Mi := prob.Mcross i
  let Ai := prob.A i
  let Bi := prob.B i
  let Δi1 := prob.Delta ⟨i.val + 1, by omega⟩
  let qi := prob.qvec ⟨i.val, by omega⟩
  let ri := prob.rvec i
  let ci1 := prob.cvec ⟨i.val + 1, by omega⟩
  { P := Qi - Mi * Ri⁻¹ * Miᵀ
    p := qi - Mi.mulVec (Ri⁻¹.mulVec ri)
    Amat := Ai - Bi * Ri⁻¹ * Miᵀ
    C := Δi1 + Bi * Ri⁻¹ * Biᵀ
    cvec := ci1 - Bi.mulVec (Ri⁻¹.mulVec ri) }

/-- Base case for the terminal stage i = N:

```
  P_{N→N+1} = Qₙ
  p_{N→N+1} = qₙ
  A_{N→N+1} = 0
  C_{N→N+1} = 0
  c_{N→N+1} = 0
```

This reflects the fact that V_{N→N+1}(xₙ, xₙ₊₁) = ½ xₙᵀ Qₙ xₙ + qₙᵀ xₙ
when xₙ₊₁ = 0, and +∞ otherwise (enforced by the singular C = 0). -/
noncomputable def ivfInitTerminal {N : ℕ}
    (prob : DualRegLQR n m N) : IntervalValueFn n :=
  { P := prob.Q ⟨N, by omega⟩
    p := prob.qvec ⟨N, by omega⟩
    Amat := 0
    C := 0
    cvec := 0 }

-- ═══════════════════════════════════════════════════════════════════════════
-- § 3. Combination Rule
-- ═══════════════════════════════════════════════════════════════════════════

/-- Combine two interval value functions V_{i→j} ⊕ V_{j→k} = V_{i→k}.

Given V_{i→j} = (P₁, p₁, A₁, C₁, c₁) ("left") and
      V_{j→k} = (P₂, p₂, A₂, C₂, c₂) ("right"),
the combined V_{i→k} has parameters:

```
  P_{i→k} = A₁ᵀ (I + P₂ C₁)⁻¹ P₂ A₁ + P₁
  p_{i→k} = A₁ᵀ (I + P₂ C₁)⁻¹ (p₂ + P₂ c₁) + p₁
  A_{i→k} = A₂ (I + C₁ P₂)⁻¹ A₁
  C_{i→k} = A₂ (I + C₁ P₂)⁻¹ C₁ A₂ᵀ + C₂
  c_{i→k} = A₂ (I + C₁ P₂)⁻¹ (c₁ − C₁ p₂) + c₂
```

These rules correspond to eliminating the shared boundary variable xⱼ
by quadratic minimization from V_{i→j}(xᵢ, xⱼ) + V_{j→k}(xⱼ, xₖ).
See arXiv:2104.03186, Theorem 1, for the full derivation. -/
noncomputable def ivfCombine (left right : IntervalValueFn n) : IntervalValueFn n :=
  let P₁ := left.P;  let p₁ := left.p;  let A₁ := left.Amat
  let C₁ := left.C;  let c₁ := left.cvec
  let P₂ := right.P; let p₂ := right.p; let A₂ := right.Amat
  let C₂ := right.C; let c₂ := right.cvec
  let F₁ := (1 + P₂ * C₁)⁻¹   -- (I + P₂ C₁)⁻¹
  let F₂ := (1 + C₁ * P₂)⁻¹   -- (I + C₁ P₂)⁻¹
  { P    := A₁ᵀ * F₁ * P₂ * A₁ + P₁
    p    := A₁ᵀ.mulVec (F₁.mulVec (p₂ + P₂.mulVec c₁)) + p₁
    Amat := A₂ * F₂ * A₁
    C    := A₂ * F₂ * C₁ * A₂ᵀ + C₂
    cvec := A₂.mulVec (F₂.mulVec (c₁ - C₁.mulVec p₂)) + c₂ }

-- ═══════════════════════════════════════════════════════════════════════════
-- § 4. Right Fold (Computing V_{i→N+1})
-- ═══════════════════════════════════════════════════════════════════════════

/-- Fold from right to left, computing the interval value function V_{N−i → N+1}.

`ivfFoldRight prob i` returns the IVF for the interval [N−i, N+1]:
- i = 0: V_{N→N+1} (terminal base case)
- i+1: combine(V_{N−1−i → N−i}, V_{N−i → N+1})

This models the sequential application of the combination rule from the
rightmost stage toward the left, equivalent to a reverse associative scan. -/
noncomputable def ivfFoldRight {N : ℕ}
    (prob : DualRegLQR n m N) : ℕ → IntervalValueFn n
  | 0 => ivfInitTerminal prob
  | i + 1 =>
    if h : i < N then
      ivfCombine (ivfInitRunning prob ⟨N - 1 - i, by omega⟩) (ivfFoldRight prob i)
    else ivfFoldRight prob i

/-
═══════════════════════════════════════════════════════════════════════════
§ 5. Combination Preserves A = C = c = 0
═══════════════════════════════════════════════════════════════════════════

When the right factor has A = 0, the combination produces A = 0.
    Proof: A_{ik} = A₂ · F₂ · A₁ = 0 · F₂ · A₁ = 0.
-/
theorem ivfCombine_Amat_zero (left right : IntervalValueFn n)
    (hA : right.Amat = 0) :
    (ivfCombine left right).Amat = 0 := by
  unfold ivfCombine; aesop;

/-
When the right factor has A = C = 0, the combination produces C = 0.
    Proof: C_{ik} = A₂ · F₂ · C₁ · A₂ᵀ + C₂ = 0 + 0 = 0.
-/
theorem ivfCombine_C_zero (left right : IntervalValueFn n)
    (hA : right.Amat = 0) (hC : right.C = 0) :
    (ivfCombine left right).C = 0 := by
  unfold ivfCombine; aesop;

/-
When the right factor has A = 0 and c = 0, the combination produces c = 0.
    Proof: c_{ik} = A₂ · F₂ · (c₁ − C₁ p₂) + c₂ = 0 + 0 = 0.
-/
theorem ivfCombine_cvec_zero (left right : IntervalValueFn n)
    (hA : right.Amat = 0) (hc : right.cvec = 0) :
    (ivfCombine left right).cvec = 0 := by
  unfold ivfCombine; aesop;

/-
═══════════════════════════════════════════════════════════════════════════
§ 6. Right Fold Always Produces A = C = c = 0
═══════════════════════════════════════════════════════════════════════════

The right fold always produces Amat = 0, since the terminal has A = 0
    and the combination preserves this.
-/
theorem ivfFoldRight_Amat_zero {N : ℕ} (prob : DualRegLQR n m N)
    (i : ℕ) (hi : i ≤ N) :
    (ivfFoldRight prob i).Amat = 0 := by
  induction' i with i ihI generalizing N;
  · rfl;
  · grind +locals

/-
The right fold always produces C = 0.
-/
theorem ivfFoldRight_C_zero {N : ℕ} (prob : DualRegLQR n m N)
    (i : ℕ) (hi : i ≤ N) :
    (ivfFoldRight prob i).C = 0 := by
  induction' i with i ih;
  · rfl;
  · rw [ ivfFoldRight ];
    split_ifs <;> simp_all +decide [ Nat.lt_succ_iff ];
    exact ivfCombine_C_zero _ _ ( ivfFoldRight_Amat_zero _ _ ( by linarith ) ) ( ih ( Nat.le_of_lt ‹_› ) )

/-
The right fold always produces cvec = 0.
-/
theorem ivfFoldRight_cvec_zero {N : ℕ} (prob : DualRegLQR n m N)
    (i : ℕ) (hi : i ≤ N) :
    (ivfFoldRight prob i).cvec = 0 := by
  induction' i with i ih <;> simp_all +decide [ ivfFoldRight ];
  · rfl;
  · grind +suggestions

/-
═══════════════════════════════════════════════════════════════════════════
§ 7. Woodbury Identity for the Parallel–Sequential Bridge
═══════════════════════════════════════════════════════════════════════════

**Woodbury identity** for the parallel Riccati recursion.

If Ĉ = Δ + B R⁻¹ Bᵀ, W = P(I + ΔP)⁻¹, and G = R + Bᵀ W B, then:

```
  (I + P Ĉ)⁻¹ P = W − W B G⁻¹ Bᵀ W
```

This bridges the parallel combination (which uses (I + PĈ)⁻¹)
with the sequential Riccati quantities W, G.

**Proof sketch**: Verify by left-multiplication:
  (I + PĈ)(W − W B G⁻¹ Bᵀ W)
  = (I + PΔ)W + P B R⁻¹ Bᵀ W − (I + PΔ)W B G⁻¹ Bᵀ W − P B R⁻¹ Bᵀ W B G⁻¹ Bᵀ W
  = P + P B (R⁻¹ − G⁻¹ − R⁻¹ Bᵀ W B G⁻¹) Bᵀ W
  = P + P B · 0 · Bᵀ W = P

where the zero follows from R⁻¹ − G⁻¹ − R⁻¹(G−R)G⁻¹ = R⁻¹ R G⁻¹ − G⁻¹ = 0.
-/
theorem woodbury_riccati
    (P Δ : Matrix (Fin n) (Fin n) ℝ)
    (B : Matrix (Fin n) (Fin m) ℝ)
    (R : Matrix (Fin m) (Fin m) ℝ)
    (hInv1 : IsUnit (1 + Δ * P))
    (hInv2 : IsUnit (1 + P * Δ))
    (hR : IsUnit R)
    (hG : IsUnit (riccatiG R B (riccatiW P Δ)))
    (hPC : IsUnit (1 + P * (Δ + B * R⁻¹ * Bᵀ))) :
    (1 + P * (Δ + B * R⁻¹ * Bᵀ))⁻¹ * P =
      riccatiW P Δ -
        riccatiW P Δ * B * (riccatiG R B (riccatiW P Δ))⁻¹ * Bᵀ *
          riccatiW P Δ := by
  have hW : ( 1 + P * Δ ) * riccatiW P Δ = P := by
    have hW : (1 + P * Δ) * P = P * (1 + Δ * P) := by
      simp +decide [ mul_add, add_mul, mul_assoc ];
    simp_all +decide [ isUnit_iff_isUnit_det ];
    unfold riccatiW; simp_all +decide [ ← mul_assoc ] ;
  have hW_inv : (1 + P * (Δ + B * R⁻¹ * Bᵀ)) * (riccatiW P Δ - riccatiW P Δ * B * (riccatiG R B (riccatiW P Δ))⁻¹ * Bᵀ * riccatiW P Δ) = P := by
    simp_all +decide [ mul_sub, ← mul_assoc, Matrix.isUnit_iff_isUnit_det ];
    simp_all +decide [ mul_add, add_mul, mul_assoc, Matrix.mul_assoc, Matrix.mul_inv_rev, riccatiW, riccatiG ];
    simp_all +decide [ ← add_assoc, ← Matrix.mul_assoc ];
    have h_inv : (R + Bᵀ * P * (1 + Δ * P)⁻¹ * B) * (R + Bᵀ * P * (1 + Δ * P)⁻¹ * B)⁻¹ = 1 := by
      exact Matrix.mul_nonsing_inv _ ( show IsUnit _ from isUnit_iff_ne_zero.mpr hG );
    simp_all +decide [ Matrix.mul_assoc, add_mul, mul_add, ← eq_sub_iff_add_eq' ];
    simp_all +decide [ mul_assoc, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul ];
    simp_all +decide [ ← Matrix.mul_assoc, ← eq_sub_iff_add_eq' ];
  rw [ ← hW_inv, ← Matrix.mul_assoc ];
  simp_all +decide [ Matrix.isUnit_iff_isUnit_det ]

/-
═══════════════════════════════════════════════════════════════════════════
§ 7b. Helper: Schur complement identity
═══════════════════════════════════════════════════════════════════════════

Core Schur complement identity relating the parallel and sequential formulas.

    Ãᵀ (W − WBG⁻¹BᵀW) Ã + (Q − MR⁻¹Mᵀ) = Q + AᵀWA − HᵀG⁻¹H

    where Ã = A − BR⁻¹Mᵀ, H = BᵀWA + Mᵀ, G = R + BᵀWB.
-/
theorem schur_complement_parallel_sequential
    (Q : Matrix (Fin n) (Fin n) ℝ) (R : Matrix (Fin m) (Fin m) ℝ)
    (M : Matrix (Fin n) (Fin m) ℝ) (A : Matrix (Fin n) (Fin n) ℝ)
    (B : Matrix (Fin n) (Fin m) ℝ) (W : Matrix (Fin n) (Fin n) ℝ)
    (hR : IsUnit R)
    (hG : IsUnit (R + Bᵀ * W * B))
    (hRs : R.IsSymm) (hWs : W.IsSymm) :
    (A - B * R⁻¹ * Mᵀ)ᵀ *
      (W - W * B * (R + Bᵀ * W * B)⁻¹ * Bᵀ * W) *
      (A - B * R⁻¹ * Mᵀ) + (Q - M * R⁻¹ * Mᵀ) =
    Q + Aᵀ * W * A +
      (Bᵀ * W * A + Mᵀ)ᵀ * (-(R + Bᵀ * W * B)⁻¹ * (Bᵀ * W * A + Mᵀ)) := by
  simp_all +decide [ Matrix.IsSymm, Matrix.mul_assoc, Matrix.mul_add, Matrix.add_mul, Matrix.sub_mul, Matrix.mul_sub, Matrix.transpose_mul, Matrix.transpose_nonsing_inv, Matrix.transpose_add, Matrix.transpose_sub ];
  have := inv_diff_decomp R ( R + Bᵀ * ( W * B ) ) ( Bᵀ * ( W * B ) ) ?_ ?_ ?_ <;> simp_all +decide [ Matrix.isUnit_iff_isUnit_det ];
  simp_all +decide [ ← Matrix.mul_assoc, ← eq_sub_iff_add_eq ];
  simp_all +decide [ Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc ] ; abel_nf;
  simp_all +decide [ ← Matrix.mul_assoc, ← eq_sub_iff_add_eq' ] ; abel_nf;
  have := inv_diff_decomp' R ( R + Bᵀ * W * B ) ( Bᵀ * W * B ) ?_ ?_ ?_ <;> simp_all +decide [ Matrix.isUnit_iff_isUnit_det ];
  simp_all +decide [ Matrix.mul_assoc, Matrix.mul_sub, Matrix.sub_mul ] ; abel_nf

/-
═══════════════════════════════════════════════════════════════════════════
§ 8. One-Step Matching: P Component
═══════════════════════════════════════════════════════════════════════════

**One-step P matching**: The P component of the parallel combination
(base-case IVF combined with the right fold) equals the sequential
backward Riccati step.

Specifically, if we combine the base-case IVF at stage k with a right IVF
that has P = P_{k+1} and C = 0, then the resulting P equals the sequential
P_k = Q + Aᵀ W A + Hᵀ K.

```
  Ã = A − B R⁻¹ Mᵀ    (reduced dynamics from base case)
  P̃ = Q − M R⁻¹ Mᵀ    (reduced Hessian from base case)
  Ĉ = Δ + B R⁻¹ Bᵀ    (augmented regularization from base case)

  Ãᵀ (I + P_{k+1} Ĉ)⁻¹ P_{k+1} Ã + P̃ = Q + Aᵀ W A + Hᵀ K
```

where W = P_{k+1}(I + Δ P_{k+1})⁻¹, G = R + Bᵀ W B, H = Bᵀ W A + Mᵀ,
K = −G⁻¹ H.
-/
theorem parallel_P_step
    (Q : Matrix (Fin n) (Fin n) ℝ) (R : Matrix (Fin m) (Fin m) ℝ)
    (M : Matrix (Fin n) (Fin m) ℝ) (A : Matrix (Fin n) (Fin n) ℝ)
    (B : Matrix (Fin n) (Fin m) ℝ) (Pnext Δ : Matrix (Fin n) (Fin n) ℝ)
    (hInv1 : IsUnit (1 + Δ * Pnext))
    (hInv2 : IsUnit (1 + Pnext * Δ))
    (hR : IsUnit R) (hRs : R.IsSymm)
    (hG : IsUnit (riccatiG R B (riccatiW Pnext Δ)))
    (hPC : IsUnit (1 + Pnext * (Δ + B * R⁻¹ * Bᵀ)))
    (hPs : Pnext.IsSymm) (hΔs : Δ.IsSymm) :
    let W := riccatiW Pnext Δ
    let G := riccatiG R B W
    let H := riccatiH M A B W
    let K := riccatiK G H
    -- Parallel formula
    (A - B * R⁻¹ * Mᵀ)ᵀ * (1 + Pnext * (Δ + B * R⁻¹ * Bᵀ))⁻¹ *
      Pnext * (A - B * R⁻¹ * Mᵀ) + (Q - M * R⁻¹ * Mᵀ) =
    -- Sequential formula
    riccatiPstep Q A W H K := by
  have hWs : (riccatiW Pnext Δ).IsSymm :=
    riccatiW_isSymm Pnext Δ hPs hΔs hInv1 hInv2
  have hw := woodbury_riccati Pnext Δ B R hInv1 hInv2 hR hG hPC;
  convert schur_complement_parallel_sequential Q R M A B ( riccatiW Pnext Δ ) hR hG hRs hWs using 1;
  simp_all +decide [ mul_assoc, Matrix.mul_sub, Matrix.sub_mul ];
  unfold riccatiG; norm_num [ Matrix.mul_assoc ] ;
  abel1

/-
═══════════════════════════════════════════════════════════════════════════
§ 9. One-Step Matching: p Component
═══════════════════════════════════════════════════════════════════════════

Helper step 2: Once we know (I+PĈ)⁻¹(p+Pc̃) = g - WBG⁻¹h,
    the p step reduces to: Ãᵀ(g - WBG⁻¹h) + p̃ = q + Aᵀg + Hᵀk.
    This holds because the difference is M·R⁻¹·(h - Bᵀg - r) = 0 (since h = r + Bᵀg).
-/
theorem parallel_p_step2
    (R : Matrix (Fin m) (Fin m) ℝ)
    (M : Matrix (Fin n) (Fin m) ℝ) (A : Matrix (Fin n) (Fin n) ℝ)
    (B : Matrix (Fin n) (Fin m) ℝ) (W : Matrix (Fin n) (Fin n) ℝ)
    (qk : Fin n → ℝ) (rvec : Fin m → ℝ) (g : Fin n → ℝ)
    (hR : IsUnit R) (hRs : R.IsSymm) (hWs : W.IsSymm)
    (hG : IsUnit (riccatiG R B W)) :
    let H := riccatiH M A B W
    let hh := rvec + Bᵀ.mulVec g
    let kk := -(riccatiG R B W)⁻¹.mulVec hh
    -- LHS: Ãᵀ(g - WBG⁻¹h) + p̃
    (A - B * R⁻¹ * Mᵀ)ᵀ.mulVec
      (g - (W * B * (riccatiG R B W)⁻¹).mulVec hh) +
      (qk - M.mulVec (R⁻¹.mulVec rvec)) =
    -- RHS: q + Aᵀg + Hᵀk
    qk + Aᵀ.mulVec g + Hᵀ.mulVec kk := by
  unfold riccatiH;
  simp +decide [ Matrix.mulVec_add, Matrix.mulVec_sub, Matrix.mulVec_neg, Matrix.mulVec_mulVec, Matrix.vecMul_mulVec, Matrix.vecMul_sub, Matrix.vecMul_add, sub_eq_add_neg, add_assoc, add_left_comm, add_comm ];
  simp +decide [ Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, Matrix.vecMul_add, Matrix.vecMul_mulVec, Matrix.vecMul_neg, Matrix.neg_mulVec, Matrix.mulVec_add, Matrix.mulVec_neg, Matrix.transpose_nonsing_inv, hRs.eq, hWs.eq ] ; ring;
  have h_inv_diff : R⁻¹ * Bᵀ * W * B * (riccatiG R B W)⁻¹ = R⁻¹ - (riccatiG R B W)⁻¹ := by
    convert inv_diff_decomp R ( riccatiG R B W ) ( Bᵀ * W * B ) hR hG _ using 1;
    · simp +decide only [Matrix.mul_assoc];
    · rfl;
  simp_all +decide [ ← Matrix.mul_assoc, ← Matrix.mulVec_mulVec ];
  simp +decide [ Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.mulVec_add, Matrix.mulVec_sub, Matrix.mulVec_mulVec, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, Matrix.mulVec_smul, Matrix.smul_mulVec, Matrix.vecMul_mulVec, Matrix.vecMul_smul, Matrix.smul_vecMul ] ; ring

/-
Helper step 1: (I+PĈ)⁻¹(p + Pc̃) = g - WBG⁻¹h.
    Proved by showing (I+PĈ) * (g - WBG⁻¹h) = p + Pc̃.
-/
theorem parallel_p_step1
    (R : Matrix (Fin m) (Fin m) ℝ)
    (B : Matrix (Fin n) (Fin m) ℝ) (Pnext Δ : Matrix (Fin n) (Fin n) ℝ)
    (pnext : Fin n → ℝ) (rvec : Fin m → ℝ) (ck1 : Fin n → ℝ)
    (hInv1 : IsUnit (1 + Δ * Pnext))
    (hInv2 : IsUnit (1 + Pnext * Δ))
    (hR : IsUnit R)
    (hG : IsUnit (riccatiG R B (riccatiW Pnext Δ)))
    (hPC : IsUnit (1 + Pnext * (Δ + B * R⁻¹ * Bᵀ))) :
    let W := riccatiW Pnext Δ
    let G := riccatiG R B W
    let ψ := ((1 + Pnext * Δ)⁻¹).mulVec pnext
    let g := ψ + W.mulVec ck1
    let hh := rvec + Bᵀ.mulVec g
    (1 + Pnext * (Δ + B * R⁻¹ * Bᵀ))⁻¹.mulVec
      (pnext + Pnext.mulVec (ck1 - B.mulVec (R⁻¹.mulVec rvec))) =
    g - (W * B * G⁻¹).mulVec hh := by
  have h_inv : ∀ (v : Fin n → ℝ), (1 + Pnext * (Δ + B * R⁻¹ * Bᵀ)) *ᵥ v = pnext + Pnext *ᵥ (ck1 - B *ᵥ R⁻¹ *ᵥ rvec) → v = (riccatiW Pnext Δ *ᵥ ck1 + (1 + Pnext * Δ)⁻¹.mulVec pnext) - (riccatiW Pnext Δ * B * (riccatiG R B (riccatiW Pnext Δ))⁻¹).mulVec (rvec + Bᵀ.mulVec (riccatiW Pnext Δ *ᵥ ck1 + (1 + Pnext * Δ)⁻¹.mulVec pnext)) := by
    have h_inv : (1 + Pnext * (Δ + B * R⁻¹ * Bᵀ)) *ᵥ ((riccatiW Pnext Δ *ᵥ ck1 + (1 + Pnext * Δ)⁻¹.mulVec pnext) - (riccatiW Pnext Δ * B * (riccatiG R B (riccatiW Pnext Δ))⁻¹).mulVec (rvec + Bᵀ.mulVec (riccatiW Pnext Δ *ᵥ ck1 + (1 + Pnext * Δ)⁻¹.mulVec pnext))) = pnext + Pnext *ᵥ (ck1 - B *ᵥ R⁻¹ *ᵥ rvec) := by
      have h_inv : (1 + Pnext * Δ) *ᵥ ((1 + Pnext * Δ)⁻¹.mulVec pnext + riccatiW Pnext Δ *ᵥ ck1) = pnext + Pnext *ᵥ ck1 := by
        simp_all +decide [ Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.isUnit_iff_isUnit_det ];
        unfold riccatiW;
        simp +decide [ Matrix.mul_assoc, Matrix.mul_add, Matrix.add_mul, Matrix.mul_nonsing_inv, hInv1, hInv2 ];
        simp +decide [ ← Matrix.mul_assoc, ← Matrix.add_mul, hInv1, hInv2 ];
        rw [ show Pnext + Pnext * Δ * Pnext = Pnext * ( 1 + Δ * Pnext ) by simp +decide [ mul_add, add_mul, mul_assoc ] ] ; simp +decide [ hInv1, hInv2, Matrix.mul_assoc ];
      have h_inv : (1 + Pnext * (Δ + B * R⁻¹ * Bᵀ)) *ᵥ ((riccatiW Pnext Δ * B * (riccatiG R B (riccatiW Pnext Δ))⁻¹).mulVec (rvec + Bᵀ.mulVec (riccatiW Pnext Δ *ᵥ ck1 + (1 + Pnext * Δ)⁻¹.mulVec pnext))) = Pnext *ᵥ B *ᵥ R⁻¹ *ᵥ (rvec + Bᵀ.mulVec (riccatiW Pnext Δ *ᵥ ck1 + (1 + Pnext * Δ)⁻¹.mulVec pnext)) := by
        have h_inv : (1 + Pnext * (Δ + B * R⁻¹ * Bᵀ)) * (riccatiW Pnext Δ * B) = Pnext * B * R⁻¹ * (riccatiG R B (riccatiW Pnext Δ)) := by
          have h_inv : (1 + Pnext * Δ) * (riccatiW Pnext Δ * B) = Pnext * B := by
            have h_inv : (1 + Pnext * Δ) * (riccatiW Pnext Δ) = Pnext := by
              have h_inv : (1 + Pnext * Δ) * (Pnext * (1 + Δ * Pnext)⁻¹) = Pnext := by
                have h_inv : (1 + Pnext * Δ) * Pnext = Pnext * (1 + Δ * Pnext) := by
                  simp +decide [ mul_add, add_mul, mul_assoc ]
                simp_all +decide [ ← mul_assoc, Matrix.isUnit_iff_isUnit_det ];
              exact h_inv;
            rw [ ← Matrix.mul_assoc, h_inv ];
          simp_all +decide [ mul_add, add_mul, Matrix.mul_assoc, riccatiG ];
          simp_all +decide [ ← Matrix.mul_assoc, Matrix.isUnit_iff_isUnit_det ];
          simp_all +decide [ mul_add, add_mul, Matrix.mul_assoc, Matrix.add_mul, Matrix.mul_add ];
          rw [ ← add_assoc, h_inv ];
        simp_all +decide [ ← Matrix.mul_assoc, Matrix.isUnit_iff_isUnit_det ];
      simp_all +decide [ Matrix.mulVec_add, Matrix.mulVec_sub, Matrix.mulVec_mulVec ];
      simp_all +decide [ Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, Matrix.mulVec_add, Matrix.mulVec_mulVec ];
      grind +suggestions;
    have h_inv : ∀ (v w : Fin n → ℝ), (1 + Pnext * (Δ + B * R⁻¹ * Bᵀ)) *ᵥ v = (1 + Pnext * (Δ + B * R⁻¹ * Bᵀ)) *ᵥ w → v = w := by
      intro v w hvw; apply_fun ( fun x => ( 1 + Pnext * ( Δ + B * R⁻¹ * Bᵀ ) ) ⁻¹ *ᵥ x ) at hvw; simp_all +decide [ Matrix.isUnit_iff_isUnit_det ] ;
    grind +locals;
  convert h_inv _ _ using 1;
  · ac_rfl;
  · cases hPC.nonempty_invertible ; aesop ( simp_config := { singlePass := true } )

/-- **One-step p matching**: The p component of the parallel combination
equals the sequential backward p step.

```
  Ãᵀ (I + P Ĉ)⁻¹ (p + P c̃) + p̃ = q + Aᵀ g + Hᵀ k
```

where:
- c̃ = c_{k+1} − B R⁻¹ r   (base-case cvec)
- p̃ = q − M R⁻¹ r          (base-case pvec)
- g = (I + PΔ)⁻¹ p + W c_{k+1}
- h = r + Bᵀ g
- k = −G⁻¹ h -/
theorem parallel_p_step
    (Q : Matrix (Fin n) (Fin n) ℝ) (R : Matrix (Fin m) (Fin m) ℝ)
    (M : Matrix (Fin n) (Fin m) ℝ) (A : Matrix (Fin n) (Fin n) ℝ)
    (B : Matrix (Fin n) (Fin m) ℝ) (Pnext Δ : Matrix (Fin n) (Fin n) ℝ)
    (pnext : Fin n → ℝ) (qk rk : Fin n → ℝ) (rvec : Fin m → ℝ)
    (ck1 : Fin n → ℝ)
    (hInv1 : IsUnit (1 + Δ * Pnext))
    (hInv2 : IsUnit (1 + Pnext * Δ))
    (hR : IsUnit R) (hRs : R.IsSymm)
    (hG : IsUnit (riccatiG R B (riccatiW Pnext Δ)))
    (hPC : IsUnit (1 + Pnext * (Δ + B * R⁻¹ * Bᵀ)))
    (hPs : Pnext.IsSymm) (hΔs : Δ.IsSymm) :
    let W := riccatiW Pnext Δ
    let G := riccatiG R B W
    let H := riccatiH M A B W
    let ψ := ((1 + Pnext * Δ)⁻¹).mulVec pnext
    let g := ψ + W.mulVec ck1
    let hh := rvec + Bᵀ.mulVec g
    let kk := -(G⁻¹).mulVec hh
    -- Parallel formula
    (A - B * R⁻¹ * Mᵀ)ᵀ.mulVec
      ((1 + Pnext * (Δ + B * R⁻¹ * Bᵀ))⁻¹.mulVec
        (pnext + Pnext.mulVec (ck1 - B.mulVec (R⁻¹.mulVec rvec)))) +
    (qk - M.mulVec (R⁻¹.mulVec rvec)) =
    -- Sequential formula
    qk + Aᵀ.mulVec g + Hᵀ.mulVec kk := by
  have hWs : (riccatiW Pnext Δ).IsSymm := riccatiW_isSymm _ _ hPs hΔs hInv1 hInv2
  have h1 := parallel_p_step1 R B Pnext Δ pnext rvec ck1 hInv1 hInv2 hR hG hPC
  simp only [] at h1
  rw [h1]
  exact parallel_p_step2 R M A B (riccatiW Pnext Δ) qk rvec
    ((1 + Pnext * Δ)⁻¹.mulVec pnext + (riccatiW Pnext Δ).mulVec ck1)
    hR hRs hWs hG

-- ═══════════════════════════════════════════════════════════════════════════
-- § 10. Full Matching by Induction
-- ═══════════════════════════════════════════════════════════════════════════

/-- Assumptions needed at backward step `i` (with `i < N`) for the parallel recursion.
    Stage index is `k = N − 1 − i`. -/
structure ParallelStageValid {N : ℕ} (prob : DualRegLQR n m N)
    (i : ℕ) (hi : i < N) (Pprev : Matrix (Fin n) (Fin n) ℝ) : Prop where
  /-- The control cost Hessian Rₖ is invertible -/
  R_inv : IsUnit (prob.R ⟨N - 1 - i, by omega⟩)
  /-- The sequential validity conditions also hold -/
  seq_valid : LQRStageValid
    (prob.toLQRStages ⟨N - 1 - i, by omega⟩) Pprev
  /-- The parallel invertibility: (I + P(Δ + BR⁻¹Bᵀ)) is invertible -/
  par_inv : IsUnit (1 + Pprev *
    (prob.Delta ⟨N - i, by omega⟩ +
     prob.B ⟨N - 1 - i, by omega⟩ *
     (prob.R ⟨N - 1 - i, by omega⟩)⁻¹ *
     (prob.B ⟨N - 1 - i, by omega⟩)ᵀ))

/-
The P component of the right fold matches the sequential backward P.
    `(ivfFoldRight prob i).P = backwardP prob i` for all i ≤ N.
-/
theorem ivfFoldRight_P_eq_backwardP {N : ℕ} (prob : DualRegLQR n m N)
    (hQN : (prob.Q ⟨N, by omega⟩).PosSemidef)
    (hValid : ∀ (j : ℕ) (hj : j < N),
      ParallelStageValid prob j hj (backwardP prob j)) :
    ∀ i, i ≤ N → (ivfFoldRight prob i).P = backwardP prob i := by
  intro i hi; induction' i with i ih <;> simp_all +decide [ Nat.sub_sub, add_comm ] ;
  · rfl;
  · rw [ show ivfFoldRight prob ( i + 1 ) = ivfCombine ( ivfInitRunning prob ⟨ N - 1 - i, by omega ⟩ ) ( ivfFoldRight prob i ) from ?_ ];
    · rw [ show backwardP prob ( i + 1 ) = riccatiPstep ( prob.Q ⟨ N - 1 - i, by omega ⟩ ) ( prob.A ⟨ N - 1 - i, by omega ⟩ ) ( riccatiW ( backwardP prob i ) ( prob.Delta ⟨ N - 1 - i + 1, by omega ⟩ ) ) ( riccatiH ( prob.Mcross ⟨ N - 1 - i, by omega ⟩ ) ( prob.A ⟨ N - 1 - i, by omega ⟩ ) ( prob.B ⟨ N - 1 - i, by omega ⟩ ) ( riccatiW ( backwardP prob i ) ( prob.Delta ⟨ N - 1 - i + 1, by omega ⟩ ) ) ) ( riccatiK ( riccatiG ( prob.R ⟨ N - 1 - i, by omega ⟩ ) ( prob.B ⟨ N - 1 - i, by omega ⟩ ) ( riccatiW ( backwardP prob i ) ( prob.Delta ⟨ N - 1 - i + 1, by omega ⟩ ) ) ) ( riccatiH ( prob.Mcross ⟨ N - 1 - i, by omega ⟩ ) ( prob.A ⟨ N - 1 - i, by omega ⟩ ) ( prob.B ⟨ N - 1 - i, by omega ⟩ ) ( riccatiW ( backwardP prob i ) ( prob.Delta ⟨ N - 1 - i + 1, by omega ⟩ ) ) ) ) from ?_ ];
      · convert parallel_P_step _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ using 1;
        all_goals first | rfl | (norm_num [ ih ( Nat.le_of_lt hi ) ]) | skip;
        · have := hValid i hi;
          convert this.seq_valid.inv1 using 1;
        · convert hValid i hi |>.seq_valid.inv2 using 1;
        · exact hValid i hi |>.R_inv;
        · exact hValid i hi |>.seq_valid.R_symm;
        · exact hValid i hi |>.seq_valid.G_inv;
        · convert hValid i hi |>.par_inv using 1;
          grind;
        · exact psd_isSymm (backwardP_posSemidef prob hQN
            (fun j hj => (hValid j hj).seq_valid) i (Nat.le_of_lt hi));
        · exact psd_isSymm (hValid i hi).seq_valid.Δ_psd;
      · rw [ backwardP ];
        rw [ riccatiBackward ] ; aesop;
    · exact dif_pos hi

/-
The p component of the right fold matches the sequential backward p.
    `(ivfFoldRight prob i).p = backwardp prob i` for all i ≤ N.
-/
theorem ivfFoldRight_p_eq_backwardp {N : ℕ} (prob : DualRegLQR n m N)
    (hQN : (prob.Q ⟨N, by omega⟩).PosSemidef)
    (hValid : ∀ (j : ℕ) (hj : j < N),
      ParallelStageValid prob j hj (backwardP prob j)) :
    ∀ i, i ≤ N → (ivfFoldRight prob i).p = backwardp prob i := by
  intro i hi; induction' i with i ih <;> simp_all +decide [ Nat.sub_sub, add_comm ] ;
  · rfl;
  · unfold ivfFoldRight backwardp; simp +decide [ hi ] ;
    convert parallel_p_step _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ using 1;
    grind +suggestions;
    exact ( ivfFoldRight prob i ).P;
    exact ( ivfFoldRight prob i ).p;
    · convert hValid i hi |>.seq_valid.inv1 using 1;
      rw [ ivfFoldRight_P_eq_backwardP prob hQN hValid i hi.le ];
      unfold DualRegLQR.toLQRStages; aesop;
    · convert hValid i hi |>.seq_valid.inv2 using 1;
      rw [ ivfFoldRight_P_eq_backwardP prob hQN hValid i hi.le ] ; norm_num [ Nat.sub_sub, add_comm ];
      unfold DualRegLQR.toLQRStages; simp +decide [ add_comm ] ;
    · exact hValid i hi |>.R_inv;
    · exact hValid i hi |>.seq_valid.R_symm;
    · convert hValid i hi |>.seq_valid.G_inv using 1;
      congr! 2;
      exact ivfFoldRight_P_eq_backwardP prob hQN hValid i hi.le;
    · convert hValid i hi |>.par_inv using 1;
      rw [ ivfFoldRight_P_eq_backwardP prob hQN hValid i hi.le ];
      grind
    · rw [ivfFoldRight_P_eq_backwardP prob hQN hValid i hi.le]
      exact psd_isSymm (backwardP_posSemidef prob hQN
        (fun j hj => (hValid j hj).seq_valid) i (Nat.le_of_lt hi));
    · exact psd_isSymm (hValid i hi).seq_valid.Δ_psd;

/-
═══════════════════════════════════════════════════════════════════════════
§ 11. Base Case Correctness
═══════════════════════════════════════════════════════════════════════════

**Base case correctness**: The stage cost at the optimal control
u* = −R⁻¹(Mᵀx + r + Bᵀy) equals the base-case IVF inner form.

Specifically, define the stage Lagrangian contribution:
```
  L(x, u, y, x') = ½ xᵀQx + xᵀMu + ½ uᵀRu + qᵀx + rᵀu
                  + yᵀ(Ax + Bu + c' − x') − ½ yᵀΔy
```

Then at u* = −R⁻¹(Mᵀx + r + Bᵀy):
```
  L(x, u*, y, x') = ½ xᵀ P̃ x + p̃ᵀ x + yᵀ(Ã x + c̃ − x') − ½ yᵀ Ĉ y + const
```

where P̃, p̃, Ã, Ĉ, c̃ are the base-case IVF parameters.
-/
theorem ivfInitRunning_base_case_correct
    (Q : Matrix (Fin n) (Fin n) ℝ) (R : Matrix (Fin m) (Fin m) ℝ)
    (M : Matrix (Fin n) (Fin m) ℝ) (A : Matrix (Fin n) (Fin n) ℝ)
    (B : Matrix (Fin n) (Fin m) ℝ) (Δ : Matrix (Fin n) (Fin n) ℝ)
    (qvec : Fin n → ℝ) (rvec : Fin m → ℝ) (cvec : Fin n → ℝ)
    (hR : IsUnit R) (hRs : R.IsSymm)
    (x x' y : Fin n → ℝ) :
    let u_star := -(R⁻¹).mulVec (Mᵀ.mulVec x + rvec + Bᵀ.mulVec y)
    -- Stage Lagrangian at optimal u
    (1/2 : ℝ) * (x ⬝ᵥ Q.mulVec x) + x ⬝ᵥ M.mulVec u_star +
      (1/2 : ℝ) * (u_star ⬝ᵥ R.mulVec u_star) +
      qvec ⬝ᵥ x + rvec ⬝ᵥ u_star +
      y ⬝ᵥ (A.mulVec x + B.mulVec u_star + cvec - x') -
      (1/2 : ℝ) * (y ⬝ᵥ Δ.mulVec y) =
    -- Base-case IVF inner form + constant
    (1/2 : ℝ) * (x ⬝ᵥ (Q - M * R⁻¹ * Mᵀ).mulVec x) +
      (qvec - M.mulVec (R⁻¹.mulVec rvec)) ⬝ᵥ x +
      y ⬝ᵥ ((A - B * R⁻¹ * Mᵀ).mulVec x +
            (cvec - B.mulVec (R⁻¹.mulVec rvec)) - x') -
      (1/2 : ℝ) * (y ⬝ᵥ (Δ + B * R⁻¹ * Bᵀ).mulVec y) +
    -- Constant term (independent of x, x', y)
    (-(1/2 : ℝ) * (rvec ⬝ᵥ R⁻¹.mulVec rvec)) := by
  simp +decide [ Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add, dotProduct_smul ];
  simp +decide [ Matrix.sub_mulVec, Matrix.add_mulVec ];
  simp +decide [ Matrix.mul_assoc, Matrix.mulVec_neg, Matrix.neg_mulVec, dotProduct_neg, neg_add_rev, add_assoc, sub_eq_add_neg ] ; ring;
  simp_all +decide [ Matrix.isUnit_iff_isUnit_det, dotProduct_comm ] ; ring;
  simp +decide [ Matrix.dotProduct_mulVec, Matrix.vecMul_mulVec, Matrix.mul_assoc, Matrix.transpose_nonsing_inv, hRs.eq ] ; ring

-- ═══════════════════════════════════════════════════════════════════════════
-- § 12. Combination Rule Correctness
-- ═══════════════════════════════════════════════════════════════════════════

/-- Evaluate an interval value function in its "outer" (C⁻¹-penalty) form:
    V̂(x, x') = ½ xᵀ P x + pᵀ x + ½ (Ax + c − x')ᵀ C⁻¹ (Ax + c − x') -/
noncomputable def ivfEval (ivf : IntervalValueFn n) (x x' : Fin n → ℝ) : ℝ :=
  (1/2 : ℝ) * (x ⬝ᵥ ivf.P.mulVec x) + ivf.p ⬝ᵥ x +
  (1/2 : ℝ) * ((ivf.Amat.mulVec x + ivf.cvec - x') ⬝ᵥ
    ivf.C⁻¹.mulVec (ivf.Amat.mulVec x + ivf.cvec - x'))

/-- The Hessian of V_L(xᵢ, xⱼ) + V_R(xⱼ, xₖ) with respect to xⱼ:
    H = C₁⁻¹ + P₂ + A₂ᵀ C₂⁻¹ A₂ -/
noncomputable def ivfCombineHessianXj (left right : IntervalValueFn n) :
    Matrix (Fin n) (Fin n) ℝ :=
  left.C⁻¹ + right.P + right.Amat.transpose * right.C⁻¹ * right.Amat

/-- The optimal intermediate state xⱼ* that minimizes V_L(xᵢ, xⱼ) + V_R(xⱼ, xₖ).

Setting the gradient to zero: H xⱼ = C₁⁻¹(A₁xᵢ+c₁) − p₂ − A₂ᵀC₂⁻¹(c₂−xₖ)
gives xⱼ* = H⁻¹ [C₁⁻¹(A₁xᵢ+c₁) − p₂ − A₂ᵀC₂⁻¹(c₂−xₖ)] -/
noncomputable def ivfCombineOptXj (left right : IntervalValueFn n)
    (xi xk : Fin n → ℝ) : Fin n → ℝ :=
  let H := ivfCombineHessianXj left right
  let rhs := left.C⁻¹.mulVec (left.Amat.mulVec xi + left.cvec)
             - right.p
             - right.Amat.transpose.mulVec (right.C⁻¹.mulVec (right.cvec - xk))
  H⁻¹.mulVec rhs

/-- The gradient of the objective V_L(xᵢ, xⱼ) + V_R(xⱼ, xₖ) w.r.t. xⱼ.

∇_xⱼ [V_L + V_R] = −C₁⁻¹(A₁xᵢ + c₁ − xⱼ) + P₂ xⱼ + p₂ + A₂ᵀ C₂⁻¹(A₂xⱼ + c₂ − xₖ)

Equivalently: H xⱼ − [C₁⁻¹(A₁xᵢ+c₁) − p₂ − A₂ᵀ C₂⁻¹(c₂−xₖ)] -/
noncomputable def ivfCombineGrad (left right : IntervalValueFn n)
    (xi xk xj : Fin n → ℝ) : Fin n → ℝ :=
  (ivfCombineHessianXj left right).mulVec xj
  - left.C⁻¹.mulVec (left.Amat.mulVec xi + left.cvec)
  + right.p
  + right.Amat.transpose.mulVec (right.C⁻¹.mulVec (right.cvec - xk))

/-- **First-order optimality**: the gradient vanishes at xⱼ*. -/
theorem ivfCombine_gradient_vanishes
    (left right : IntervalValueFn n)
    (hH : IsUnit (ivfCombineHessianXj left right))
    (xi xk : Fin n → ℝ) :
    ivfCombineGrad left right xi xk (ivfCombineOptXj left right xi xk) = 0 := by
  unfold ivfCombineGrad ivfCombineOptXj ivfCombineHessianXj;
  simp_all +decide [ Matrix.isUnit_iff_isUnit_det ];
  rw [ Matrix.mul_nonsing_inv _ ];
  · ext i; norm_num; ring;
  · exact isUnit_iff_ne_zero.mpr hH

/-- For symmetric M: ½ (a+b)ᵀ M (a+b) − ½ aᵀ M a = a ⬝ᵥ M b + ½ b ⬝ᵥ M b -/
theorem quadDiff_symm (M : Matrix (Fin n) (Fin n) ℝ) (a b : Fin n → ℝ)
    (hM : M.IsSymm) :
    (1/2 : ℝ) * ((a + b) ⬝ᵥ M.mulVec (a + b)) -
    (1/2 : ℝ) * (a ⬝ᵥ M.mulVec a) =
    a ⬝ᵥ M.mulVec b + (1/2 : ℝ) * (b ⬝ᵥ M.mulVec b) := by
  grind +suggestions

/-- **Completing the square for the combination rule.**

For all xⱼ:
  V_L(xᵢ, xⱼ) + V_R(xⱼ, xₖ)
  = V_L(xᵢ, xⱼ*) + V_R(xⱼ*, xₖ) + ½ (xⱼ − xⱼ*)ᵀ H (xⱼ − xⱼ*)

where xⱼ* = `ivfCombineOptXj left right xi xk` and
H = `ivfCombineHessianXj left right`. -/
theorem ivfCombine_completing_square
    (left right : IntervalValueFn n)
    (hCLinvS : left.C⁻¹.IsSymm) (hPRS : right.P.IsSymm)
    (hCRinvS : right.C⁻¹.IsSymm)
    (hH : IsUnit (ivfCombineHessianXj left right))
    (xi xk xj : Fin n → ℝ) :
    let xj_opt := ivfCombineOptXj left right xi xk
    let H := ivfCombineHessianXj left right
    let δ := xj - xj_opt
    ivfEval left xi xj + ivfEval right xj xk =
    ivfEval left xi xj_opt + ivfEval right xj_opt xk +
    (1/2 : ℝ) * (δ ⬝ᵥ H.mulVec δ) := by
  unfold ivfEval;
  have hxj_opt : (ivfCombineHessianXj left right).mulVec (ivfCombineOptXj left right xi xk) = (left.C⁻¹.mulVec (left.Amat.mulVec xi + left.cvec) - right.p - right.Amat.transpose.mulVec (right.C⁻¹.mulVec (right.cvec - xk))) := by
    unfold ivfCombineOptXj;
    simp_all +decide [ Matrix.isUnit_iff_isUnit_det ];
  unfold ivfCombineHessianXj at *;
  simp_all +decide [ Matrix.add_mulVec, Matrix.mulVec_add, Matrix.mulVec_sub, Matrix.sub_mulVec, dotProduct_sub, dotProduct_add, dotProduct_smul ];
  simp_all +decide [ ← eq_sub_iff_add_eq', Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_mulVec, Matrix.mul_assoc, Matrix.transpose_mul, Matrix.transpose_nonsing_inv, Matrix.IsSymm ];
  simp_all +decide [ ← Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec, ← Matrix.vecMul_mulVec, Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_mulVec, Matrix.mul_assoc, Matrix.transpose_mul, Matrix.transpose_nonsing_inv, Matrix.IsSymm ];
  ring;
  norm_num [ dotProduct_comm ]

/-- **Minimality corollary**: when H is positive semidefinite,
xⱼ* minimizes V_L(xᵢ, xⱼ) + V_R(xⱼ, xₖ). -/
theorem ivfCombine_is_minimum
    (left right : IntervalValueFn n)
    (hCLinvS : left.C⁻¹.IsSymm) (hPRS : right.P.IsSymm)
    (hCRinvS : right.C⁻¹.IsSymm)
    (hH : IsUnit (ivfCombineHessianXj left right))
    (hHpsd : (ivfCombineHessianXj left right).PosSemidef)
    (xi xk xj : Fin n → ℝ) :
    ivfEval left xi xj + ivfEval right xj xk ≥
    ivfEval left xi (ivfCombineOptXj left right xi xk) +
    ivfEval right (ivfCombineOptXj left right xi xk) xk := by
  have := ivfCombine_completing_square left right hCLinvS hPRS hCRinvS hH xi xk xj; simp_all +decide [ Matrix.IsSymm, Matrix.PosSemidef ] ;
  have := hHpsd.2 ( Finsupp.equivFunOnFinite.symm ( xj - ivfCombineOptXj left right xi xk ) ) ; simp_all +decide [ Finsupp.sum_fintype, Matrix.mulVec, dotProduct ] ;
  simp_all +decide [ mul_assoc, mul_sub, sub_mul, Finset.mul_sum _ _ _, Finset.sum_mul ] ; linarith;

-- ═══════════════════════════════════════════════════════════════════════════
-- § 13. Connection: V_{i→N+1}(xᵢ, 0) = Vᵢ(xᵢ)
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Key observation**: Since the right fold produces A = C = c = 0,
the interval value function V_{i→N+1}(xᵢ, xₙ₊₁) reduces to
½ xᵢᵀ P xᵢ + pᵀ xᵢ (plus a constant, which is 0 at xₙ₊₁ = 0).

In particular, the cost-to-go Vᵢ(xᵢ) = V_{i→N+1}(xᵢ, 0) has Hessian P
and linear term p matching the sequential backward Riccati. -/
theorem ivfFoldRight_eval_at_zero_eq_costToGo {N : ℕ}
    (prob : DualRegLQR n m N)
    (hQN : (prob.Q ⟨N, by omega⟩).PosSemidef)
    (hValid : ∀ (j : ℕ) (hj : j < N),
      ParallelStageValid prob j hj (backwardP prob j))
    (i : ℕ) (hi : i ≤ N) (x : Fin n → ℝ) :
    -- V_{N-i→N+1}(x, 0) has Hessian and linear term matching sequential
    (1/2 : ℝ) * (x ⬝ᵥ (ivfFoldRight prob i).P.mulVec x) +
      (ivfFoldRight prob i).p ⬝ᵥ x =
    (1/2 : ℝ) * (x ⬝ᵥ (backwardP prob i).mulVec x) +
      (backwardp prob i) ⬝ᵥ x := by
  rw [ivfFoldRight_P_eq_backwardP prob hQN hValid i hi,
      ivfFoldRight_p_eq_backwardp prob hQN hValid i hi]

-- ═══════════════════════════════════════════════════════════════════════════
-- § 14. Main Theorem
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Main Theorem (Parallel Riccati Recursion)**

For the dual-regularized LQR problem, the parallel Riccati recursion
computes the same cost-to-go value functions as the sequential backward
Riccati recursion.

### Interval Value Function Definitions

For i ∈ {0, …, N−1} (running stages), the length-1 IVFs have:
```
  P_{i→i+1} = Qᵢ − Mᵢ Rᵢ⁻¹ Mᵢᵀ
  p_{i→i+1} = qᵢ − Mᵢ Rᵢ⁻¹ rᵢ
  A_{i→i+1} = Aᵢ − Bᵢ Rᵢ⁻¹ Mᵢᵀ
  C_{i→i+1} = Δᵢ₊₁ + Bᵢ Rᵢ⁻¹ Bᵢᵀ
  c_{i→i+1} = cᵢ₊₁ − Bᵢ Rᵢ⁻¹ rᵢ
```

For the terminal stage:
```
  P_{N→N+1} = Qₙ,  p_{N→N+1} = qₙ,  A = C = c = 0
```

### Combination Rules

Given V_{i→j} and V_{j→k}, the combined V_{i→k} has:
```
  P_{i→k} = A₁ᵀ (I + P₂ C₁)⁻¹ P₂ A₁ + P₁
  p_{i→k} = A₁ᵀ (I + P₂ C₁)⁻¹ (p₂ + P₂ c₁) + p₁
  A_{i→k} = A₂ (I + C₁ P₂)⁻¹ A₁
  C_{i→k} = A₂ (I + C₁ P₂)⁻¹ C₁ A₂ᵀ + C₂
  c_{i→k} = A₂ (I + C₁ P₂)⁻¹ (c₁ − C₁ p₂) + c₂
```

### Matching with Sequential

When folded from right to left, the interval V_{i→N+1} satisfies:
1. A_{i→N+1} = C_{i→N+1} = c_{i→N+1} = 0
2. P_{i→N+1} = Pᵢ (the sequential backward Riccati Hessian)
3. p_{i→N+1} = pᵢ (the sequential backward Riccati linear term)

Therefore Vᵢ(xᵢ) = V_{i→N+1}(xᵢ, 0) = ½ xᵢᵀ Pᵢ xᵢ + pᵢᵀ xᵢ + Vᵢ(0),
where Pᵢ is symmetric and positive semidefinite. -/
theorem parallel_riccati_main {N : ℕ} (prob : DualRegLQR n m N)
    (hQN : (prob.Q ⟨N, by omega⟩).PosSemidef)
    (hValid : ∀ (j : ℕ) (hj : j < N),
      ParallelStageValid prob j hj (backwardP prob j)) :
    -- Part 1: Right fold produces zero A, C, c components
    (∀ i, i ≤ N → (ivfFoldRight prob i).Amat = 0) ∧
    (∀ i, i ≤ N → (ivfFoldRight prob i).C = 0) ∧
    (∀ i, i ≤ N → (ivfFoldRight prob i).cvec = 0) ∧
    -- Part 2: P component matches sequential
    (∀ i, i ≤ N → (ivfFoldRight prob i).P = backwardP prob i) ∧
    -- Part 3: p component matches sequential
    (∀ i, i ≤ N → (ivfFoldRight prob i).p = backwardp prob i) ∧
    -- Part 4: Pᵢ is PSD (from the sequential theorem)
    (∀ i, i ≤ N → (ivfFoldRight prob i).P.PosSemidef) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun i hi => ivfFoldRight_Amat_zero prob i hi
  · exact fun i hi => ivfFoldRight_C_zero prob i hi
  · exact fun i hi => ivfFoldRight_cvec_zero prob i hi
  · exact fun i hi => ivfFoldRight_P_eq_backwardP prob hQN hValid i hi
  · exact fun i hi => ivfFoldRight_p_eq_backwardp prob hQN hValid i hi
  · intro i hi
    rw [ivfFoldRight_P_eq_backwardP prob hQN hValid i hi]
    exact backwardP_posSemidef prob hQN
      (fun j hj => (hValid j hj).seq_valid) i hi