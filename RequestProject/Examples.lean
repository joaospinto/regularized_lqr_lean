/-
# Worked examples from the paper

This file formalizes the two `\begin{example}` blocks of
"Dual-Regularized Riccati Recursions for Interior-Point Optimal Control"
(Sousa-Pinto & Orban).

## Example 1 — correct inertia with an indefinite stage Hessian

A scalar problem with `N = 1`, `Q₀ = 1`, `M₀ = 0`, `R₀ = -1`, `Q₁ = 1`,
dynamics `x₁ = 2u₀`, and dual regularization `Δ₀ = Δ₁ = 1`. The stage Hessian
`[[Q₀, M₀], [M₀ᵀ, R₀]] = [[1,0],[0,-1]]` is **indefinite** (`R₀` is not positive
definite), yet the first-order optimality matrix `K_LQR = [[P, Cᵀ], [C, -Δ]]`
still has the correct inertia `(3, 2, 0)`, because the reduced Schur complement
`P + Cᵀ Δ⁻¹ C` is positive definite. This illustrates that the usual
positive-(semi)definiteness assumptions are sufficient but **not necessary**
(cf. `\label{riccati-rational-identity-theorem}` and the discussion preceding it).

The relevant data are
`P = diag(1, -1, 1)`, `C = [[-1,0,0],[0,2,-1]]`, `Δ = I`, and
`P + Cᵀ Δ⁻¹ C = [[2,0,0],[0,3,-2],[0,-2,2]]` with leading principal minors
`2, 6, 4`, hence positive definite.
-/
import Mathlib
import RequestProject.KKTInertia

open Matrix KKTInertia

namespace PaperExamples

/-- `P = diag(1, -1, 1)` — the (indefinite) stage Hessian of Example 1. -/
def exP : Matrix (Fin 3) (Fin 3) ℝ := !![1, 0, 0; 0, -1, 0; 0, 0, 1]

/-- `C = [[-1,0,0],[0,2,-1]]` — the constraint (initial-state + dynamics) matrix. -/
def exC : Matrix (Fin 2) (Fin 3) ℝ := !![-1, 0, 0; 0, 2, -1]

/-- `Δ = I₂` — the dual regularization. -/
def exΔ : Matrix (Fin 2) (Fin 2) ℝ := 1

/-
The reduced Schur complement `P + Cᵀ Δ⁻¹ C = [[2,0,0],[0,3,-2],[0,-2,2]]`.
-/
theorem ex1_schur_eq :
    exP + exCᵀ * exΔ⁻¹ * exC = !![2, 0, 0; 0, 3, -2; 0, -2, 2] := by
  unfold exP exC exΔ; norm_num [ Matrix.inv_def ] ;
  ext i j ; fin_cases i <;> fin_cases j <;> norm_num [ Matrix.mul_apply ]

/-
The reduced Schur complement is positive definite (leading minors `2, 6, 4`).
-/
theorem ex1_schur_posDef :
    (exP + exCᵀ * exΔ⁻¹ * exC).PosDef := by
  -- The matrix !![2, 0, 0; 0, 3, -2; 0, -2, 2] is positive definite because its leading principal minors are all positive.
  have h_pos_def : ∀ x : Fin 3 → ℝ, x ≠ 0 → 0 < x ⬝ᵥ (Matrix.of ![![2, 0, 0], ![0, 3, -2], ![0, -2, 2]] : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ x := by
    intro x hx_ne_zero
    have h_quad_form : x 0 ^ 2 * 2 + x 1 ^ 2 * 3 + x 2 ^ 2 * 2 - x 1 * x 2 * 4 > 0 := by
      by_cases h_x0 : x 0 = 0;
      · by_cases h_x1 : x 1 = 0 <;> by_cases h_x2 : x 2 = 0 <;> simp_all +decide [ funext_iff, Fin.forall_fin_succ ];
        · positivity;
        · positivity;
        · nlinarith [ sq_nonneg ( x 1 - x 2 ), mul_self_pos.2 h_x1, mul_self_pos.2 h_x2 ];
      · nlinarith [ sq_nonneg ( x 1 - x 2 ), mul_self_pos.2 h_x0 ];
    convert h_quad_form.lt using 1 ; norm_num [ Fin.sum_univ_succ, Matrix.mulVec ] ; ring!;
  rw [ ex1_schur_eq ];
  constructor;
  · ext i j; fin_cases i <;> fin_cases j <;> rfl;
  · intro x hx; specialize h_pos_def ( x ) ; simp_all +decide [ Finsupp.sum_fintype,  dotProduct ] ;
    convert h_pos_def using 1 ; norm_num [ Fin.sum_univ_succ ] ; ring!

/-
**Example 1.** Even though the stage Hessian `[[1,0],[0,-1]]` is indefinite,
the first-order optimality matrix `K_LQR = [[P, Cᵀ], [C, -Δ]]` has the correct
inertia `(3, 2, 0)`.
-/
theorem ex1_inertia :
    HasInertia (fromBlocks exP exCᵀ exC (-exΔ)) 3 2 0 := by
  convert ( kkt_inertia_iff exP exC exΔ _ _ ) |>.mpr ex1_schur_posDef using 1;
  · ext i j; fin_cases i <;> fin_cases j <;> rfl;
  · convert Matrix.PosDef.one; all_goals infer_instance

/-
## Example 2 — dual regularization is necessary for descent

A two-stage unconstrained LQR problem with states `(x₀, x₁)` and control `u₀`,
cost `½(x₀² + u₀² + x₁²)`, dynamics `x₁ = x₀ + u₀`, initial state `s₀ = 0`. At the
primal iterate `(x₀, u₀, x₁) = (0, 0, 1)` and dual iterate `(y₀, y₁) = (0, 3)`,
the **un-regularized** Newton-KKT system `[[I, Cᵀ], [C, 0]]` (no dual
regularization) has solution `(Δx₀, Δu₀, Δx₁, Δy₀, Δy₁) = (0, 0, -1, 0, -3)`, and
the directional derivative of the Augmented Lagrangian merit function along the
primal direction equals `2 - η`. Hence `η > 2` is required for the computed
direction to be a descent direction — illustrating that without dual
regularization the Newton step need not descend the merit function (contrast with
`\label{inertia-al-descent-theorem}`).
-/

namespace Example2

/-- The constraint matrix `C = [[-1,0,0],[1,1,-1]]` (initial-state row and
dynamics row). -/
def C2 : Matrix (Fin 2) (Fin 3) ℝ := !![-1, 0, 0; 1, 1, -1]

/-- The (un-regularized) `5×5` Newton-KKT matrix `[[I, Cᵀ], [C, 0]]`. -/
def K2 : Matrix (Fin 5) (Fin 5) ℝ :=
  !![ 1, 0, 0, -1,  1;
      0, 1, 0,  0,  1;
      0, 0, 1,  0, -1;
     -1, 0, 0,  0,  0;
      1, 1,-1,  0,  0]

/-- The Newton step solution `(Δx₀, Δu₀, Δx₁, Δy₀, Δy₁) = (0,0,-1,0,-3)`. -/
def sol2 : Fin 5 → ℝ := ![0, 0, -1, 0, -3]

/-- The right-hand side `(-3, -3, 2, 0, 1)` (i.e. `-∇L`). -/
def rhs2 : Fin 5 → ℝ := ![-3, -3, 2, 0, 1]

/-
The given vector solves the Newton-KKT linear system.
-/
theorem ex2_solves : K2 *ᵥ sol2 = rhs2 := by
  ext i;
  fin_cases i <;> simp +decide [ K2, sol2, rhs2, Matrix.mulVec, dotProduct, Fin.sum_univ_succ ] ; norm_num

/-- The primal Newton direction `Δx = (Δx₀, Δu₀, Δx₁) = (0, 0, -1)`. -/
def dx2 : Fin 3 → ℝ := ![0, 0, -1]

/-- Current primal iterate `x = (0, 0, 1)`. -/
def x2 : Fin 3 → ℝ := ![0, 0, 1]

/-- Current dual iterate `y = (0, 3)`. -/
def y2 : Fin 2 → ℝ := ![0, 3]

/-- Gradient of the Augmented Lagrangian merit function with penalty `η`:
`∇ₓ𝒜 = ∇f(x) + Cᵀ y + η Cᵀ c(x)`, where `∇f(x) = x` and `c(x) = C x`. -/
noncomputable def gradA (eta : ℝ) : Fin 3 → ℝ :=
  x2 + C2ᵀ *ᵥ y2 + eta • (C2ᵀ *ᵥ (C2 *ᵥ x2))

/-
**Example 2.** The directional derivative of the Augmented Lagrangian merit
function along the primal Newton direction equals `2 - η`.
-/
theorem ex2_directional_derivative (eta : ℝ) :
    gradA eta ⬝ᵥ dx2 = 2 - eta := by
  unfold gradA; norm_num [ dotProduct, Matrix.mulVec ] ; ring;
  unfold C2 x2 y2 dx2; norm_num [ Fin.sum_univ_succ, Matrix.mul_apply ] ; ring;

/-- Consequently, the Newton direction descends the merit function (negative
directional derivative) **iff** the penalty satisfies `η > 2`. -/
theorem ex2_descent_iff (eta : ℝ) :
    gradA eta ⬝ᵥ dx2 < 0 ↔ 2 < eta := by
  rw [ex2_directional_derivative]; constructor <;> intro h <;> linarith

end Example2

end PaperExamples