/-
# The Zariski-density principle behind the rational-identity theorem

This file formalizes the mathematical core of the *rational-identity* theorem of
"Dual-Regularized Riccati Recursions for Interior-Point Optimal Control"
(Sousa-Pinto & Orban), `\label{riccati-rational-identity-theorem}`.

That theorem states that, whenever the first-order optimality matrix is
nonsingular and the Riccati recursions are well-defined, the recursions return
the *unique* solution of the linear system — even without the usual
positive-(semi)definiteness assumptions.  The paper's proof is a Zariski-density
argument: every component returned by the recursions, and every component of the
direct solution `-K⁻¹ [s; c]`, is a rational function of the problem data; the
two rational functions agree on the nonempty open set where the stronger
assumptions hold (where the derivation of the recursions applies); hence, after
clearing denominators, their difference is a polynomial vanishing on a nonempty
open set, so it is identically zero, and the two rational functions coincide
everywhere both are defined.

The combinatorial/topological heart of this argument is:

> a polynomial that vanishes on a nonempty open subset of `ℝᵏ` is identically
> zero,

equivalently, two polynomials agreeing on a nonempty open set are equal
(`mvPolynomial_eq_of_eqOn_open`).  We then package the rational-function
consequence the proof actually uses: two rational expressions `p/d` and `q/d`
(with a common denominator `d`) that agree throughout a nonempty open set on
which `d` is nonzero agree at *every* point where `d` is nonzero
(`ratIdentity_of_eqOn_open`).

This is exactly the abstract principle the paper invokes; instantiating it at the
explicit Riccati recursions (writing each recursion output as a rational function
of the data) is a routine but very large bookkeeping task that we do not carry
out here.

We use Mathlib's `MvPolynomial.funext_set`: two polynomials agreeing on a box
with infinite sides are equal.  A nonempty open set in `ℝᵏ` (with the sup metric)
contains such a box, namely an open `ε`-ball around an interior point.
-/
import Mathlib

set_option maxHeartbeats 1000000

open MvPolynomial
open scoped Topology

namespace RationalIdentity

/-- A nonempty open set of `Fin k → ℝ` contains an open box with infinite sides
(an `ε`-ball around an interior point in the sup metric). -/
theorem exists_infinite_box_subset {k : ℕ} {U : Set (Fin k → ℝ)}
    (hU : IsOpen U) {x₀ : Fin k → ℝ} (hx₀ : x₀ ∈ U) :
    ∃ s : Fin k → Set ℝ, (∀ i, (s i).Infinite) ∧ Set.pi Set.univ s ⊆ U := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU x₀ hx₀
  refine ⟨fun i => Set.Ioo (x₀ i - ε) (x₀ i + ε), fun i => ?_, ?_⟩
  · exact Set.Ioo_infinite (by linarith)
  · intro x hx
    apply hball
    simp only [Set.mem_pi, Set.mem_univ, Set.mem_Ioo, forall_true_left] at hx
    rw [Metric.mem_ball, dist_pi_lt_iff hε]
    intro i
    rw [Real.dist_eq, abs_sub_lt_iff]
    constructor <;> [linarith [(hx i).2]; linarith [(hx i).1]]

/-- **Identity theorem for real multivariate polynomials.**
Two polynomials over `ℝ` that agree on a nonempty open set are equal. -/
theorem mvPolynomial_eq_of_eqOn_open {k : ℕ} (p q : MvPolynomial (Fin k) ℝ)
    {U : Set (Fin k → ℝ)} (hU : IsOpen U) {x₀ : Fin k → ℝ} (hx₀ : x₀ ∈ U)
    (h : ∀ x ∈ U, eval x p = eval x q) : p = q := by
  obtain ⟨s, hs, hsU⟩ := exists_infinite_box_subset hU hx₀
  exact MvPolynomial.funext_set s hs (fun x hx => h x (hsU hx))

/-- **Polynomial values agree everywhere** once two polynomials agree on a
nonempty open set. -/
theorem eval_eq_of_eqOn_open {k : ℕ} (p q : MvPolynomial (Fin k) ℝ)
    {U : Set (Fin k → ℝ)} (hU : IsOpen U) {x₀ : Fin k → ℝ} (hx₀ : x₀ ∈ U)
    (h : ∀ x ∈ U, eval x p = eval x q) (x : Fin k → ℝ) :
    eval x p = eval x q := by
  rw [mvPolynomial_eq_of_eqOn_open p q hU hx₀ h]

/-- **Rational-identity principle** (the form used in the proof of
`\label{riccati-rational-identity-theorem}`).

Let `p, q` be polynomials in the problem data and `d` a common denominator.
If the two rational expressions `p/d` and `q/d` agree throughout a nonempty open
set `U` on which `d` does not vanish — this is the open set where the Riccati
derivation's positive-definiteness assumptions hold — then they agree at *every*
point where `d` is nonzero.

Here `p` plays the role of the (numerator of a component of the) Riccati output,
`q` that of the direct solution `-K⁻¹[s;c]`, and `d` a common denominator (a
product of the pivots / the determinant of `K`). -/
theorem ratIdentity_of_eqOn_open {k : ℕ} (p q d : MvPolynomial (Fin k) ℝ)
    {U : Set (Fin k → ℝ)} (hU : IsOpen U) {x₀ : Fin k → ℝ} (hx₀ : x₀ ∈ U)
    (hd : ∀ x ∈ U, eval x d ≠ 0)
    (h : ∀ x ∈ U, eval x p / eval x d = eval x q / eval x d) :
    ∀ x : Fin k → ℝ, eval x d ≠ 0 → eval x p / eval x d = eval x q / eval x d := by
  have hpq : p = q := by
    refine mvPolynomial_eq_of_eqOn_open p q hU hx₀ (fun x hx => ?_)
    have := h x hx
    field_simp [hd x hx] at this
    exact this
  intro x _
  rw [hpq]

end RationalIdentity
