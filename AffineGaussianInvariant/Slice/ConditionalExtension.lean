import AffineGaussianInvariant.Invariant.UnitaryFFTStatement

set_option autoImplicit false

namespace AffineGaussianInvariant

universe u v w x

section

variable {𝕜 : Type u} [Field 𝕜]
variable {GlobalInvariant : Type v} [AddCommGroup GlobalInvariant]
  [Module 𝕜 GlobalInvariant]
variable {SliceInvariant : Type w} [AddCommGroup SliceInvariant]
  [Module 𝕜 SliceInvariant]
variable {Diagram : Type x}

variable
  (data : SliceExtensionData (𝕜 := 𝕜)
    (GlobalInvariant := GlobalInvariant)
    (SliceInvariant := SliceInvariant)
    (Diagram := Diagram))

/-- Extending each diagram and restricting recovers the finite slice combination. -/
theorem restrict_globalValue
    (c : DiagramCombination 𝕜 Diagram) :
    data.restrict (c.globalValue data) = c.sliceValue data := by
  classical
  simp [DiagramCombination.globalValue, DiagramCombination.sliceValue,
    data.restrict_globalDiagram]

/-- Conditional A-S6, with the unitary tensor FFT as an explicit hypothesis. -/
theorem sliceRestriction_surjective_of_unitaryTensorFFT
    (hFFT : UnitaryTensorFFT data) :
    Function.Surjective data.restrict := by
  intro q
  obtain ⟨c, hc⟩ := hFFT q
  refine ⟨c.globalValue data, ?_⟩
  rw [restrict_globalValue]
  exact hc

end

end AffineGaussianInvariant
