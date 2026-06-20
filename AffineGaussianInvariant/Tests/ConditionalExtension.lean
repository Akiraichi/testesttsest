import AffineGaussianInvariant.Slice.ConditionalExtension

set_option autoImplicit false

namespace AffineGaussianInvariant.Tests

/-- A one-coordinate regression model for the finite-sum assembly. -/
def scalarData : SliceExtensionData (𝕜 := ℚ)
    (GlobalInvariant := ℚ) (SliceInvariant := ℚ) (Diagram := Unit) where
  restrict := LinearMap.id
  globalDiagram := fun _ => 1
  sliceDiagram := fun _ => 1
  restrict_globalDiagram := by intro d; rfl

/-- The single scalar diagram spans the one-coordinate slice. -/
theorem scalar_unitaryTensorFFT : UnitaryTensorFFT scalarData := by
  intro q
  let c : DiagramCombination ℚ Unit := {
    numberOfTerms := 1
    coefficient := fun _ => q
    diagram := fun _ => ()
  }
  refine ⟨c, ?_⟩
  simp [c, DiagramCombination.sliceValue, scalarData]

/-- Smoke test for conditional restriction surjectivity. -/
theorem scalar_restriction_surjective : Function.Surjective scalarData.restrict :=
  sliceRestriction_surjective_of_unitaryTensorFFT scalarData scalar_unitaryTensorFFT

end AffineGaussianInvariant.Tests
