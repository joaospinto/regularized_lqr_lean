# Dockerfile for building and checking the Lean formalization
#
# Usage:
#   docker build -t regularized-lqr-lean .
#   docker run --rm regularized-lqr-lean
#
# The build stage fetches Mathlib and compiles the project.
# The default CMD prints the axioms used by the main module.

FROM ubuntu:24.04 AS builder

# Install dependencies
RUN apt-get update && apt-get install -y --no-install-recommends \
    curl git ca-certificates cmake python3 \
    && rm -rf /var/lib/apt/lists/*

# Install elan (Lean version manager)
RUN curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y --default-toolchain none
ENV PATH="/root/.elan/bin:${PATH}"

# Copy project files
WORKDIR /project
COPY lean-toolchain lakefile.toml lake-manifest.json ./

# Fetch Mathlib cache (this is the slow step; cached by Docker layer)
RUN lake exe cache get

# Copy source files
COPY RequestProject/ RequestProject/

# Build the full project
RUN lake build

# ── Runtime stage ──────────────────────────────────────────────
# Re-use the same image (Lean toolchain is needed for `lake env lean`)
FROM builder

# By default, verify axioms of the main module
CMD ["sh", "-c", "echo '✅ Build succeeded. Checking axioms...' && lake env lean -run RequestProject/CheckAxioms.lean"]
