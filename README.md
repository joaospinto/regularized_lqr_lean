This project was edited by [Aristotle](https://aristotle.harmonic.fun).

To cite Aristotle:
- Tag @Aristotle-Harmonic on GitHub PRs/issues
- Add as co-author to commits:
```
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
```

# Dual-Regularized Riccati Recursions for Interior-Point Optimal Control

Lean 4 formalization of the results from
*"Dual-Regularized Riccati Recursions for Interior-Point Optimal Control"*
(Sousa-Pinto & Orban).

All theorems are fully proved (zero `sorry` statements) with only standard axioms
(`propext`, `Classical.choice`, `Quot.sound`).

## Checking the Proofs

### Option 1: Docker (no local Lean installation needed)

The simplest way to verify everything:

```bash
docker build -t regularized-lqr-lean .
docker run --rm regularized-lqr-lean
```

This fetches Lean 4 and Mathlib inside the container, builds the full project, and
confirms all proofs are machine-checked. The first build takes a while (~10–20 min)
because it downloads the Mathlib cache.

### Option 2: Local build with `elan` + `lake`

1. **Install [`elan`](https://github.com/leanprover/elan)** (Lean version manager):
   ```bash
   curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh
   ```

2. **Fetch the Mathlib cache** (avoids recompiling Mathlib from source):
   ```bash
   lake exe cache get
   ```

3. **Build the project:**
   ```bash
   lake build
   ```

4. **Check axioms of a specific theorem** (optional):
   ```bash
   lake env lean -c - <<< '#print axioms DualRegLQR.backwardP_PosSemidef'
   ```

### Option 3: GitHub Actions (CI)

If you host on GitHub, add the workflow file `.github/workflows/lean.yml`
(included in this repository) to automatically verify the proofs on every push.

### Quick reference

| Command | Description |
|---------|-------------|
| `make build` | Build the project locally |
| `make docker` | Build & verify inside Docker |
| `make axioms T=<name>` | Print axioms of a specific theorem |
| `make clean` | Remove build artifacts |

## File Organization

### Core Mathematical Helpers

| File | Lines | Contents |
|------|-------|----------|
| `MatrixHelpers.lean` | ~140 | PSD utilities (real matrices) + matrix inverse identities (Lemma 2) |
| `QuadraticLemmas.lean` | ~130 | Quadratic maximization (Lemma 1) + minimization with penalty (Lemma 3) |
| `AffineAssoc.lean` | ~35 | Associativity of affine function composition |
| `ParallelHelpers.lean` | ~140 | dot-product/mulVec identities, completing the square, Schur complement |

### Sequential Algorithm

| File | Lines | Contents |
|------|-------|----------|
| `SequentialRiccati.lean` | ~1030 | **Main file.** Riccati formula definitions (W, G, H, K), PSD preservation (Theorem 2), cost-to-go correctness (Theorem 3), p-recurrence corollary |
| `DualRegLQR.lean` | ~395 | Problem definition (`DualRegLQR` structure), backward recursion (`backwardP/p/Const`), optimal solution recovery, full PSD theorem |
| `ForwardPass.lean` | ~330 | Sequential + parallel forward pass definitions, equivalence proof |

### Parallel Algorithm

| File | Lines | Contents |
|------|-------|----------|
| `ParallelRiccati.lean` | ~870 | Parallel backward pass via interval value functions, combination rules, correctness proofs matching sequential Riccati |

### Interior-Point Method

| File | Lines | Contents |
|------|-------|----------|
| `IPMEquivalence.lean` | ~100 | KKT system reduction to 2×2 block form |
| `DescentDirection.lean` | ~195 | Descent direction theorem (Theorem 1) |

### Entry Point

| File | Contents |
|------|----------|
| `Main.lean` | Top-level module importing all components |

## Dependency Graph

```
MatrixHelpers
    │
    ▼
SequentialRiccati ◄── QuadraticLemmas (standalone)
    │
    ▼
DualRegLQR
    │
    ├──────────────────┐
    ▼                  ▼
ForwardPass        ParallelRiccati
    │                  │
    ◄─ AffineAssoc     ◄─ ParallelHelpers

IPMEquivalence (standalone)
DescentDirection (standalone)
```

## What Is Proved

1. **Theorem 1** (Descent Direction): The IPM search direction is a descent direction
   for the augmented barrier-Lagrangian.

2. **Theorem 2** (PSD Preservation): The backward Riccati recursion preserves
   positive semidefiniteness of the cost-to-go Hessian Pₖ.

3. **Theorem 3** (Cost-to-Go Correctness): The Riccati optimal (u*, x'*, y*) form
   a saddle point of the one-step Lagrangian, and the saddle-point value equals the
   Riccati cost-to-go V_k(x) = ½ xᵀPₖx + pₖᵀx + constₖ.

4. **Parallel Equivalence**: The parallel backward pass (via interval value functions
   and associative scan) produces the same Pₖ and pₖ as the sequential recursion.

5. **Forward Pass Equivalence**: The parallel forward pass (via affine composition
   scan) produces the same states, controls, and duals as the sequential forward pass.

6. **IPM System Equivalence**: The 4-equation KKT system reduces to a 2×2 block
   system in (Δx, Δs).

7. **Corollary** (p-recurrence): The alternative form
   pₖ = qₖ + Kₖᵀrₖ + (Aₖ + BₖKₖ)ᵀgₖ₊₁.

---

This project was edited by [Aristotle](https://aristotle.harmonic.fun).

To cite Aristotle:
- Tag @Aristotle-Harmonic on GitHub PRs/issues
- Add as co-author to commits:
```
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
```
