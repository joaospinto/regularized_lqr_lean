/-
# Why only the stage pivots `Gₖ` need to be checked

This file answers a follow-up question about the inertia characterization in
`KKTInertia.lean` / `KKT_INERTIA_ANALYSIS.md`:

> Why is it sufficient to check the stage pivots `Gₖ` and *not also* the
> co-state / smoothing pivots `(Pₖ + Δₖ⁻¹)` (equivalently `I + Δ^{1/2}PₖΔ^{1/2}`)?

The block `LDLᵀ` (Riccati) factorization of the reduced Hessian
`S = P + Cᵀ Δ⁻¹ C` produces two *families* of diagonal pivots:

* **co-state / smoothing pivots** — the blocks `-Δₖ` that get eliminated, and the
  resulting smoothing operators which (up to congruence) are `Pₖ + Δₖ⁻¹`;
* **stage pivots** — the control Hessians `Gₖ = Rₖ + Bₖᵀ Wₖ₊₁ Bₖ` and the final
  initial-state pivot.

By Sylvester's law `S ≻ 0` iff *all* of these pivots are positive definite. The
point is that the first family is **unconditionally** definite under the standing
hypotheses (`Δ ≻ 0` and the cost-to-go Hessians `P ⪰ 0`), so it contributes
nothing to the test. The two lemmas below make this precise.

Everything here is proved with no `sorry`.
-/
import Mathlib

open Matrix

namespace SmoothingPivot

/-- **The smoothing pivot never needs checking.**

When the cost-to-go Hessian `P` is positive *semi*definite and the dual
regularization `Δ` is positive definite, the smoothing pivot `P + Δ⁻¹` is
automatically positive *definite*. It is the strictly positive definite term
`Δ⁻¹` that makes the sum strictly definite, regardless of `P` — there is nothing
about the data that could make this pivot fail. (Congruence by `Δ^{1/2}` turns
`P + Δ⁻¹` into `I + Δ^{1/2} P Δ^{1/2}`, i.e. identity plus a PSD matrix, which is
the same observation.) -/
theorem smoothing_pivot_posDef {N : ℕ}
    (P Δ : Matrix (Fin N) (Fin N) ℝ)
    (hP : P.PosSemidef) (hΔ : Δ.PosDef) :
    (P + Δ⁻¹).PosDef :=
  PosDef.posSemidef_add hP hΔ.inv

/-- **The co-state pivot never needs checking.**

The co-state block `-Δ` is negative definite exactly because `Δ` is positive
definite, which is a standing hypothesis. (Negative definiteness of `-Δ` is, by
definition, positive definiteness of `-(-Δ) = Δ`.) So each co-state pivot
contributes precisely one negative direction with no condition on the data. -/
theorem costate_pivot_negDef {N : ℕ}
    (Δ : Matrix (Fin N) (Fin N) ℝ) (hΔ : Δ.PosDef) :
    (-(-Δ)).PosDef := by
  simpa using hΔ

end SmoothingPivot
