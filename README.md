# JSP-000523 proof

The [paper](paper/proof.pdf) and Lean formalization are by Yilin Liu. See [CONTRIBUTIONS.md](CONTRIBUTIONS.md) for contributions and AI use.

[MainTheorem.lean](JSP523/MainTheorem.lean) proves the rank-three bound, the eventual exact formula for each fixed rank at least four, and the coefficient-one forcing asymptotic for every fixed rank at least three. Rank-four stability and the equality classifications are also formalized; see the [theorem index](FORMALIZATION_STATUS.md).

## Build

With `elan` installed, run from the repository root:

```bash
lake exe cache get
lake build JSP523
bash scripts/check_no_sorry.sh
```

Lean 4.34.0 and Mathlib dependencies are pinned. `JSP523.lean` imports all modules and is built by CI on pushes and pull requests.
