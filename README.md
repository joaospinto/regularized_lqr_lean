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

---

This project was edited by [Aristotle](https://aristotle.harmonic.fun).

To cite Aristotle:
- Tag @Aristotle-Harmonic on GitHub PRs/issues
- Add as co-author to commits:
```
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
```
