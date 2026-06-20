import Mathlib

set_option autoImplicit false

namespace AffineGaussianInvariant

universe u v w x

/-- A finite linear combination of pairing diagrams. -/
structure DiagramCombination
    (𝕜 : Type u) (Diagram : Type x) where
  numberOfTerms : ℕ
  coefficient : Fin numberOfTerms → 𝕜
  diagram : Fin numberOfTerms → Diagram

section

variable {𝕜 : Type u} [Field 𝕜]
variable {GlobalInvariant : Type v} [AddCommGroup GlobalInvariant]
  [Module 𝕜 GlobalInvariant]
variable {SliceInvariant : Type w} [AddCommGroup SliceInvariant]
  [Module 𝕜 SliceInvariant]
variable {Diagram : Type x}

/-- Data supplied after individual pairing diagrams have global extensions. -/
structure SliceExtensionData where
  restrict : GlobalInvariant →ₗ[𝕜] SliceInvariant
  globalDiagram : Diagram → GlobalInvariant
  sliceDiagram : Diagram → SliceInvariant
  restrict_globalDiagram : ∀ d, restrict (globalDiagram d) = sliceDiagram d

namespace DiagramCombination

/-- Evaluate a diagram combination after applying the global extension. -/
def globalValue
    (c : DiagramCombination 𝕜 Diagram)
    (data : SliceExtensionData (𝕜 := 𝕜)
      (GlobalInvariant := GlobalInvariant)
      (SliceInvariant := SliceInvariant)
      (Diagram := Diagram)) : GlobalInvariant :=
  ∑ i, c.coefficient i • data.globalDiagram (c.diagram i)

/-- Evaluate the same combination on the fixed Williamson slice. -/
def sliceValue
    (c : DiagramCombination 𝕜 Diagram)
    (data : SliceExtensionData (𝕜 := 𝕜)
      (GlobalInvariant := GlobalInvariant)
      (SliceInvariant := SliceInvariant)
      (Diagram := Diagram)) : SliceInvariant :=
  ∑ i, c.coefficient i • data.sliceDiagram (c.diagram i)

end DiagramCombination

/--
The explicit conditional input from Claims S6.3--S6.5: every invariant on the
fixed slice is a finite linear combination of symmetrized pairing diagrams.
This does not assume a global extension or a right inverse to restriction.
-/
def UnitaryTensorFFT
    (data : SliceExtensionData (𝕜 := 𝕜)
      (GlobalInvariant := GlobalInvariant)
      (SliceInvariant := SliceInvariant)
      (Diagram := Diagram)) : Prop :=
  ∀ q : SliceInvariant,
    ∃ c : DiagramCombination 𝕜 Diagram, c.sliceValue data = q

end

end AffineGaussianInvariant
