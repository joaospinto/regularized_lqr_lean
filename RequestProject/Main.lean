/-
# Dual-Regularized Riccati Recursions for Interior-Point Optimal Control

Top-level module that imports all components of the formalization.

## File Organization

### Core Mathematical Helpers
- `MatrixHelpers`      — PSD utilities + matrix inverse identities (`inverse-helper`)
- `QuadraticLemmas`    — Quadratic optimization lemmas (`eliminate-y`, `eliminate-x`)
- `AffineAssoc`        — Associativity of affine function composition
- `ParallelHelpers`    — Matrix/vector identities for parallel proofs

### Sequential Algorithm
- `SequentialRiccati`  — Riccati definitions, PSD preservation & cost-to-go
                         correctness (`main-seq-theorem`), p-recurrence
                         corollary (`p-recurrence`)
- `DualRegLQR`         — Problem definition, backward recursion, PSD theorem
- `ForwardPass`        — Sequential + parallel forward pass, equivalence proof

### Parallel Algorithm
- `ParallelRiccati`    — Parallel backward pass via interval value functions

### Interior-Point Method
- `IPMEquivalence`     — KKT system reduction to 2×2 block form
- `DescentDirection`   — Inertia-based descent of the Augmented Barrier-Lagrangian
                         merit function (`inertia-al-descent-theorem`), with the
                         supporting `sylvester-inertia-lemma`,
                         `4x4-primal-inertia-lemma`, and
                         `al-directional-derivative-lemma`

### Inertia certification & worked examples
- `InertiaChain`        — intermediate block-elimination inertia lemma
                         (`3x3-2x2-inertia-lemma`)
- `Examples`            — the two worked `\begin{example}` blocks of the paper:
                         correct inertia with an indefinite stage Hessian, and
                         the necessity of dual regularization for descent

### Inertia certification of the Newton-KKT system
- `InertiaCertification` — the `4x4-3x3-inertia-lemma` (`In(K₄) = In(K₃) + (n_g,0,0)`)
                         via a positive-pivot Sylvester variant, and the
                         `K₄ ↔ LQR` inertia equivalence relating `K₄`'s
                         descent-certifying inertia to that of the reduced LQR
                         first-order matrix `K_{xy}`
- `RiccatiCertification` — `riccati-inertia-certification-theorem`: given the
                         Riccati block-`LDLᵀ` factorization of the reduced
                         Hessian, `K_LQR` has the correct inertia iff every stage
                         pivot is positive definite; plus reusable congruence /
                         reindexing / block-diagonal positive-definiteness lemmas
- `BlockTridiagLDL`     — the block-`LDLᵀ` factorization itself, proved (no longer
                         assumed): a symmetric block-tridiagonal matrix is positive
                         definite iff every Schur (Riccati) pivot is, by induction
                         with `2×2` Schur complements; gives the inertia
                         certification with the factorization derived
- `RationalIdentity`    — the Zariski-density core of
                         `riccati-rational-identity-theorem`: real polynomials
                         agreeing on a nonempty open set are equal, and the
                         common-denominator rational consequence
- `RationalClosure`     — the inductive part of `riccati-rational-identity-theorem`:
                         "rational function of the data" is a subring closed under
                         `+,-,*`, division, determinant, adjugate and **matrix
                         inverse**, so every recursion output is rational without
                         writing it out; plus the rational-identity conclusion

### First-Order System Inertia
- `KKTInertia`         — Inertia of the dual-regularized KKT matrix; the FOC have
                         inertia `(N(n+m)+n, (N+1)n, 0)` iff the reduced
                         (Schur-complement) Hessian `P + Cᵀ Δ⁻¹ C` is positive
                         definite (equivalently, all Riccati stage pivots `Gₖ ≻ 0`)
- `SmoothingPivot`     — Why only the stage pivots `Gₖ` need to be checked: the
                         co-state pivots `-Δₖ` and smoothing pivots `Pₖ + Δₖ⁻¹`
                         are unconditionally definite under `Δ ≻ 0`, `P ⪰ 0`

### Algebraic Properties
- `IVFAssoc`           — Associativity of IVF combination rule

### Cross-stage variables (arrowhead solve)
- `CrossStageVariables`  — the *Cross-Stage Variables* section: the arrowhead
                         Newton system `[[K, J_θ], [J_θᵀ, H_θθ]]` is solved by the
                         dense Schur complement `S_θ = H_θθ − J_θᵀ K⁻¹ J_θ`; the
                         recovered `(Δw, Δθ)` is proved to solve the system for any
                         invertible Riccati block `K` and invertible `S_θ`

-/

import RequestProject.MatrixHelpers
import RequestProject.QuadraticLemmas
import RequestProject.AffineAssoc
import RequestProject.ParallelHelpers
import RequestProject.SequentialRiccati
import RequestProject.DualRegLQR
import RequestProject.ForwardPass
import RequestProject.ParallelRiccati
import RequestProject.IPMEquivalence
import RequestProject.DescentDirection
import RequestProject.IVFAssoc
import RequestProject.KKTInertia
import RequestProject.InertiaChain
import RequestProject.SmoothingPivot
import RequestProject.Examples
import RequestProject.InertiaCertification
import RequestProject.RiccatiCertification
import RequestProject.BlockTridiagLDL
import RequestProject.RationalIdentity
import RequestProject.RationalClosure
import RequestProject.CrossStageVariables
import RequestProject.ResidualComputation
