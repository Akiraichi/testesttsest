# Dependency DAG

```text
S6.3 unitary block pairing generation
  + S6.4 polarization/restitution
  + S6.5 product blocks and slot symmetrization
        │
        ▼
UnitaryTensorFFT data  [explicit hypothesis]

S6.6 diagramwise extension identity
        │
        ▼
restrict_globalValue  [kernel-checked target]
        │
        ├────────────── UnitaryTensorFFT data
        ▼
sliceRestriction_surjective_of_unitaryTensorFFT
```

There is no circular dependency: `UnitaryTensorFFT` asserts finite pairing span, not a global extension or right inverse.
