/-
# Rational functions of the data: closure under the recursion's operations

This file carries out the inductive part of the *rational-identity* theorem
(`\label{riccati-rational-identity-theorem}`) of "Dual-Regularized Riccati
Recursions for Interior-Point Optimal Control".

The previous development (`RationalIdentity.lean`) formalized the Zariski-density
*principle* (two real multivariate polynomials agreeing on a nonempty open set are
equal). What was left out — described in the paper as "routine but very large" —
was instantiating it at the Riccati recursion. Following the suggestion to avoid
ever writing an explicit rational function, we do this *non-constructively*: we
introduce the predicate `IsRat f`, "the scalar quantity `f` is a rational
function of the problem data", and prove that it is preserved by **every operation
the recursion uses**:

* it contains the constants and the coordinate projections (the raw data);
* it is closed under `+`, `-`, `*` (it is a subring `ratSubring`);
* it is closed under division by a generically-nonzero rational function
  (`IsRat.div`);
* consequently every entry of a determinant (`IsRat.det`), every entry of an
  adjugate (`IsRat.adjugate_entry`), and — the operation the paper singles out —
  every entry of a **matrix inverse** (`IsRat.inv_entry`) is again rational.

By structural induction, every quantity produced by the recursion, and every
component of the direct solution `−K⁻¹[s;c]`, is therefore rational, *without ever
exhibiting the rational function explicitly*.

Finally `isRat_eqGen_of_eqOn_open` packages the conclusion: two rational functions
of the data that agree on a nonempty open set (the set where the strong
positive-definiteness assumptions hold, where the recursion's derivation applies)
agree at *every* data point where both are defined. This is exactly the paper's
rational-identity theorem.
-/
import Mathlib
import RequestProject.RationalIdentity

set_option maxHeartbeats 1000000

open MvPolynomial Matrix
open scoped Topology

namespace RationalClosure

variable {K : ℕ}

/-- `f` is a **rational function of the data** `x : Fin K → ℝ`: there are
polynomials `p` (numerator) and `q ≠ 0` (denominator) with `f x = p(x)/q(x)`
wherever `q(x) ≠ 0`. We use the cleared-denominator form `f x · q(x) = p(x)` to
avoid division. -/
def IsRat (f : (Fin K → ℝ) → ℝ) : Prop :=
  ∃ p q : MvPolynomial (Fin K) ℝ, q ≠ 0 ∧ ∀ x, eval x q ≠ 0 → f x * eval x q = eval x p

/-- `f` is a **generically-nonzero** rational function: rational with a nonzero
numerator (so `f` does not vanish on a dense set). This is the precondition under
which division by `f` stays rational. -/
def IsRatNZ (f : (Fin K → ℝ) → ℝ) : Prop :=
  ∃ p q : MvPolynomial (Fin K) ℝ, q ≠ 0 ∧ p ≠ 0 ∧
    ∀ x, eval x q ≠ 0 → f x * eval x q = eval x p

theorem IsRatNZ.toIsRat {f : (Fin K → ℝ) → ℝ} (hf : IsRatNZ f) : IsRat f := by
  obtain ⟨p, q, hq, _, h⟩ := hf; exact ⟨p, q, hq, h⟩

/-! ## Subring structure -/

theorem isRat_zero : IsRat (0 : (Fin K → ℝ) → ℝ) := by
  exact ⟨ 0, 1, by norm_num ⟩

theorem isRat_one : IsRat (1 : (Fin K → ℝ) → ℝ) := by
  exact ⟨ 1, 1, by norm_num ⟩

theorem IsRat.add {f g : (Fin K → ℝ) → ℝ} (hf : IsRat f) (hg : IsRat g) :
    IsRat (f + g) := by
  rcases hf with ⟨ p_f, q_f, hq_f, hf ⟩
  rcases hg with ⟨ p_g, q_g, hq_g, hg ⟩
  refine ⟨ p_f * q_g + p_g * q_f, q_f * q_g, mul_ne_zero hq_f hq_g, fun x hx => ?_ ⟩
  rw [map_mul] at hx
  obtain ⟨hxf, hxg⟩ := mul_ne_zero_iff.mp hx
  simp only [Pi.add_apply, map_add, map_mul]
  rw [← hf x hxf, ← hg x hxg]; ring

theorem IsRat.neg {f : (Fin K → ℝ) → ℝ} (hf : IsRat f) : IsRat (-f) := by
  obtain ⟨p_f, q_f, hq_f, hp_f⟩ := hf;
  refine ⟨-p_f, q_f, hq_f, fun x hx => ?_⟩
  simp only [Pi.neg_apply, map_neg, neg_mul]
  rw [hp_f x hx]

theorem IsRat.mul {f g : (Fin K → ℝ) → ℝ} (hf : IsRat f) (hg : IsRat g) :
    IsRat (f * g) := by
  obtain ⟨ p₁, q₁, hq₁, hp₁ ⟩ := hf
  obtain ⟨ p₂, q₂, hq₂, hp₂ ⟩ := hg;
  use p₁ * p₂, q₁ * q₂; simp_all +decide [ mul_assoc ] ;
  exact fun x hx₁ hx₂ => by rw [ ← hp₁ x hx₁, ← hp₂ x hx₂ ] ; ring;

theorem IsRat.sub {f g : (Fin K → ℝ) → ℝ} (hf : IsRat f) (hg : IsRat g) :
    IsRat (f - g) := by
  rw [sub_eq_add_neg]; exact hf.add hg.neg

/-- The rational functions of the data form a subring of the function ring. -/
def ratSubring (K : ℕ) : Subring ((Fin K → ℝ) → ℝ) where
  carrier := {f | IsRat f}
  zero_mem' := isRat_zero
  one_mem' := isRat_one
  add_mem' := IsRat.add
  mul_mem' := IsRat.mul
  neg_mem' := IsRat.neg

@[simp] theorem mem_ratSubring {f : (Fin K → ℝ) → ℝ} : f ∈ ratSubring K ↔ IsRat f := Iff.rfl

/-! ## Generators: constants and coordinates -/

theorem isRat_const (c : ℝ) : IsRat (fun _ : Fin K → ℝ => c) := by
  exact ⟨ MvPolynomial.C c, 1, by norm_num ⟩

theorem isRat_coord (i : Fin K) : IsRat (fun x : Fin K → ℝ => x i) := by
  exact ⟨ MvPolynomial.X i, 1, by norm_num ⟩

/-! ## Sums, products, determinants, adjugates -/

theorem IsRat.sum {ι : Type*} (s : Finset ι) (f : ι → (Fin K → ℝ) → ℝ)
    (hf : ∀ i ∈ s, IsRat (f i)) : IsRat (fun x => ∑ i ∈ s, f i x) := by
  convert Subring.sum_mem _ _;
  convert Iff.rfl;
  convert mem_ratSubring;
  rotate_left;
  exact ι;
  exacts [ s, f, fun i hi => hf i hi, by simp +decide [ Finset.sum_apply ] ]

theorem IsRat.prod {ι : Type*} (s : Finset ι) (f : ι → (Fin K → ℝ) → ℝ)
    (hf : ∀ i ∈ s, IsRat (f i)) : IsRat (fun x => ∏ i ∈ s, f i x) := by
  convert Subring.prod_mem ( ratSubring K ) _;
  rotate_left;
  exact ι;
  exacts [ s, f, fun i hi => by simpa using hf i hi, by simp +decide [ Finset.prod_apply ] ]

/-- The pointwise matrix `M x` whose `(i,j)` entry is `M i j x`. -/
def matrixAt {ι : Type*} (M : Matrix ι ι ((Fin K → ℝ) → ℝ)) (x : Fin K → ℝ) :
    Matrix ι ι ℝ := Matrix.of (fun i j => M i j x)

/-
The determinant of a matrix with rational entries is rational.
-/
theorem IsRat.det {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ((Fin K → ℝ) → ℝ)) (hM : ∀ i j, IsRat (M i j)) :
    IsRat (fun x => (matrixAt M x).det) := by
  simp +decide only [matrixAt, det_apply'];
  apply IsRat.sum;
  intro σ _;
  convert IsRat.mul ( isRat_const ( σ.sign : ℝ ) ) ( IsRat.prod Finset.univ ( fun i => M ( σ i ) i ) fun i _ => hM _ _ ) using 1

/-
Each entry of the adjugate of a matrix with rational entries is rational.
-/
theorem IsRat.adjugate_entry {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ((Fin K → ℝ) → ℝ)) (hM : ∀ i j, IsRat (M i j)) (i j : ι) :
    IsRat (fun x => (matrixAt M x).adjugate i j) := by
  unfold matrixAt;
  simp +decide [ Matrix.adjugate_apply, Matrix.det_apply' ];
  apply IsRat.sum;
  intro σ _;
  apply IsRat.mul;
  · exact isRat_const _;
  · apply IsRat.prod;
    intro k _; by_cases hk : σ k = j <;> simp +decide [ hk, hM ] ;
    exact isRat_const _

/-! ## Division and matrix inverse -/

/-
Division by a generically-nonzero rational function stays rational.
-/
theorem IsRat.div {f g : (Fin K → ℝ) → ℝ} (hf : IsRat f) (hg : IsRatNZ g) :
    IsRat (fun x => f x / g x) := by
  obtain ⟨ p_f, q_f, hq_f, hf ⟩ := hf
  obtain ⟨ p_g, q_g, hq_g, hp_g, hg ⟩ := hg
  use p_f * MvPolynomial.C (1 : ℝ) * q_g * q_g, q_f * MvPolynomial.C (1 : ℝ) * q_g * p_g;
  simp_all +decide;
  grind

/-
**The recursion's matrix-inverse step preserves rationality.** If a matrix has
rational entries and its determinant is a generically-nonzero rational function
(i.e. the matrix is invertible on a dense set, as it is on the open set where the
strong assumptions hold), then every entry of its inverse is rational.
-/
theorem IsRat.inv_entry {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ((Fin K → ℝ) → ℝ)) (hM : ∀ i j, IsRat (M i j))
    (hdet : IsRatNZ (fun x => (matrixAt M x).det)) (i j : ι) :
    IsRat (fun x => (matrixAt M x)⁻¹ i j) := by
  convert IsRat.div ( IsRat.adjugate_entry M hM i j ) hdet using 1;
  simp +decide [ div_eq_inv_mul, Matrix.inv_def ]

/-! ## Establishing generic-nonzeroness from an open set -/

/-
A nonzero polynomial is nonvanishing on a dense set.
-/
theorem dense_setOf_eval_ne {q : MvPolynomial (Fin K) ℝ} (hq : q ≠ 0) :
    Dense {x : Fin K → ℝ | eval x q ≠ 0} := by
  apply_rules [ dense_iff_inter_open.mpr ];
  intro U hU hUne
  by_contra h;
  simp_all +decide [ Set.Nonempty ];
  exact hq <| MvPolynomial.funext fun x => by simpa using RationalIdentity.eval_eq_of_eqOn_open q 0 hU hUne.choose_spec ( fun x hx => by simp +decide [ h x hx ] ) x;

/-
A rational function that is nonzero throughout a nonempty open set is
generically nonzero (its numerator does not vanish identically).
-/
theorem IsRat.toNZ_of_openNe {f : (Fin K → ℝ) → ℝ} (hf : IsRat f)
    {U : Set (Fin K → ℝ)} (hU : IsOpen U) {x₀ : Fin K → ℝ} (hx₀ : x₀ ∈ U)
    (hne : ∀ x ∈ U, f x ≠ 0) : IsRatNZ f := by
  obtain ⟨ p, q, hq, h ⟩ := hf;
  obtain ⟨ x₁, hx₁ ⟩ := ( dense_setOf_eval_ne hq ).inter_open_nonempty U hU ⟨ x₀, hx₀ ⟩;
  exact ⟨ p, q, hq, by specialize h x₁ hx₁.2; aesop, h ⟩

/-! ## The rational-identity theorem -/

/-
**Rational-identity theorem** (`\label{riccati-rational-identity-theorem}`).

Two rational functions of the data that agree throughout a nonempty open set agree
at *every* data point where both are defined: there is a common nonzero denominator
`q` such that `f x = g x` wherever `q(x) ≠ 0`.

Applied to the Riccati recursion: every component returned by the recursion and
every component of the direct solution `−K⁻¹[s;c]` is rational (by the closure
lemmas above, established by structural induction without writing the rational
functions explicitly); on the nonempty open set where the strong
positive-definiteness assumptions hold, the recursion's derivation shows the two
agree; hence they agree at every instance where both are defined.
-/
theorem isRat_eqGen_of_eqOn_open {f g : (Fin K → ℝ) → ℝ}
    (hf : IsRat f) (hg : IsRat g)
    {U : Set (Fin K → ℝ)} (hU : IsOpen U) {x₀ : Fin K → ℝ} (hx₀ : x₀ ∈ U)
    (hfg : ∀ x ∈ U, f x = g x) :
    ∃ q : MvPolynomial (Fin K) ℝ, q ≠ 0 ∧ ∀ x, eval x q ≠ 0 → f x = g x := by
  obtain ⟨ p₁, q₁, hq₁_ne_zero, h₁ ⟩ := hf
  obtain ⟨ p₂, q₂, hq₂_ne_zero, h₂ ⟩ := hg
  set p₃ : MvPolynomial (Fin K) ℝ := p₁ * q₂
  set q₃ : MvPolynomial (Fin K) ℝ := p₂ * q₁;
  -- Consider the open set `U' := U ∩ {x | eval x q_f ≠ 0} ∩ {x | eval x q_g ≠ 0}`.
  have hU' : ∃ x₁ ∈ U, (eval x₁ q₁) ≠ 0 ∧ (eval x₁ q₂) ≠ 0 := by
    have h_dense : Dense {x : Fin K → ℝ | eval x (q₁ * q₂) ≠ 0} := by
      apply dense_setOf_eval_ne; simp [hq₁_ne_zero, hq₂_ne_zero];
    have := h_dense.inter_open_nonempty U hU ⟨ x₀, hx₀ ⟩ ; obtain ⟨ x₁, hx₁₁, hx₁₂ ⟩ := this; use x₁; aesop;
  -- By `RationalIdentity.mvPolynomial_eq_of_eqOn_open` (with the open nonempty `U''` and a point in it), `p₃ = q₃` as polynomials.
  have hpq : p₃ = q₃ := by
    apply RationalIdentity.mvPolynomial_eq_of_eqOn_open;
    any_goals exact hU'.choose;
    any_goals exact U ∩ { x | ( eval x ) q₁ ≠ 0 } ∩ { x | ( eval x ) q₂ ≠ 0 };
    · exact IsOpen.inter ( IsOpen.inter hU <| isOpen_ne.preimage <| MvPolynomial.continuous_eval _ ) <| isOpen_ne.preimage <| MvPolynomial.continuous_eval _;
    · exact ⟨ ⟨ hU'.choose_spec.1, hU'.choose_spec.2.1 ⟩, hU'.choose_spec.2.2 ⟩;
    · grind;
  refine' ⟨ q₁ * q₂, mul_ne_zero hq₁_ne_zero hq₂_ne_zero, fun x hx => _ ⟩;
  replace hpq := congr_arg ( MvPolynomial.eval x ) hpq; simp_all +decide ;
  grind

end RationalClosure