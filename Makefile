.PHONY: build check clean docker

# Build the full project with Lake
build:
	lake build

# Check axioms of a specific theorem (usage: make axioms T=theorem_name)
axioms:
	lake env lean -c - <<< '#print axioms $(T)'

# Remove build artifacts
clean:
	lake clean

# Build and run inside Docker (no local Lean installation needed)
docker:
	docker build -t regularized-lqr-lean .
	docker run --rm regularized-lqr-lean
