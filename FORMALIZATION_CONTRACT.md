# Formalization contract: conditional A-S6

## Target

Kernel-check the implication

> unitary pairing-span theorem on a fixed Williamson slice + diagramwise global extension ⇒ surjectivity of the restriction map.

## TeX correspondence

- `UnitaryTensorFFT data`: output of Claims S6.3--S6.5, finite spanning by symmetrized blockwise pairing diagrams.
- `SliceExtensionData.restrict_globalDiagram`: Claim S6.6 for an individual diagram.
- `restrict_globalValue`: finite linear assembly of Claim S6.6.
- `sliceRestriction_surjective_of_unitaryTensorFFT`: Lemma A-S6 with S6.3--S6.5 explicit as a hypothesis.

## Guarantee

This milestone checks the downstream proof edge in Lean's kernel. It does not prove the unitary tensor FFT, the polynomial projector identities, polynomiality of the covariants, or the vector-slot/symmetric-power bridge.
