# Conditional formalization of the Williamson-slice extension argument

This Lean 4 project implements the p27 conditional milestone for A-S6. It kernel-checks the construction of a global invariant from a finite combination of slice pairing diagrams, assuming the unitary tensor FFT output explicitly.

Run:

```bash
lake update
lake exe cache get
lake build
lake env lean AffineGaussianInvariant/Audit/ConditionalTheorems.lean
```

The full S6.3 theorem is not claimed in this release.