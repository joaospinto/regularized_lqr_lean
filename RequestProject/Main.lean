/-
# Dual-Regularized Riccati Recursions for Interior-Point Optimal Control

Top-level module that imports all components of the formalization.

## File Organization

### Core Mathematical Helpers
- `MatrixHelpers`      — PSD utilities + matrix inverse identities (Lemma 2)
- `QuadraticLemmas`    — Quadratic optimization lemmas (Lemmas 1 & 3)
- `AffineAssoc`        — Associativity of affine function composition
- `ParallelHelpers`    — Matrix/vector identities for parallel proofs

### Sequential Algorithm
- `SequentialRiccati`  — Riccati definitions, PSD preservation (Thm 2),
                         cost-to-go correctness (Thm 3), p-recurrence corollary
- `DualRegLQR`         — Problem definition, backward recursion, PSD theorem
- `ForwardPass`        — Sequential + parallel forward pass, equivalence proof

### Parallel Algorithm
- `ParallelRiccati`    — Parallel backward pass via interval value functions

### Interior-Point Method
- `IPMEquivalence`     — KKT system reduction to 2×2 block form
- `DescentDirection`   — Descent direction theorem (Theorem 1)
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
