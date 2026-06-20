import AffineGaussianInvariant.InvariantTheory.MixedTensor.PairingFunctionals

set_option autoImplicit false

namespace AffineGaussianInvariant.InvariantTheory.MixedTensor

universe u v

section

variable (K : Type u) [Field K]
variable (V : Type v) [AddCommGroup V] [Module K V]
variable (p : ℕ)

/-- Additivity and homogeneity in every primal slot. -/
def IsPrimalMultilinear (F : Functional K V p) : Prop :=
  (∀ (i : Fin p) (x : PrimalTuple K V p) (φ : DualTuple K V p) (u v : V),
      F (Function.update x i (u + v)) φ =
        F (Function.update x i u) φ + F (Function.update x i v) φ) ∧
  (∀ (i : Fin p) (x : PrimalTuple K V p) (φ : DualTuple K V p) (a : K) (u : V),
      F (Function.update x i (a • u)) φ =
        a * F (Function.update x i u) φ)

/-- Additivity and homogeneity in every dual slot. -/
def IsDualMultilinear (F : Functional K V p) : Prop :=
  (∀ (i : Fin p) (x : PrimalTuple K V p) (φ : DualTuple K V p)
      (f g : Module.Dual K V),
      F x (Function.update φ i (f + g)) =
        F x (Function.update φ i f) + F x (Function.update φ i g)) ∧
  (∀ (i : Fin p) (x : PrimalTuple K V p) (φ : DualTuple K V p)
      (a : K) (f : Module.Dual K V),
      F x (Function.update φ i (a • f)) =
        a * F x (Function.update φ i f))

/-- Separate multilinearity in all primal and dual slots. -/
def IsMixedMultilinear (F : Functional K V p) : Prop :=
  IsPrimalMultilinear K V p F ∧ IsDualMultilinear K V p F

/--
The balanced mixed-tensor first fundamental theorem in the exact form needed
for the complexified block of Claim S6.3.

This is a proposition, not an axiom and not a theorem in the present library.
Closing it requires a proof that every invariant separately multilinear
functional lies in the span of complete contractions.
-/
def FFTStatement : Prop :=
  ∀ F : Functional K V p,
    IsMixedMultilinear K V p F →
    IsInvariant K V p F →
    IsPairingGenerated K V p F

/-- The nontrivial direction of the FFT is exactly a span-surjectivity statement. -/
theorem fftStatement_iff :
    FFTStatement K V p ↔
      ∀ F : Functional K V p,
        IsMixedMultilinear K V p F →
        IsInvariant K V p F →
        ∃ c : PairingCombination K p, ∀ x φ, F x φ = c.eval K V p x φ :=
  Iff.rfl

/-- The reverse containment, pairing span into invariants, is unconditional. -/
theorem pairingGenerated_implies_invariant
    (F : Functional K V p)
    (hF : IsPairingGenerated K V p F) :
    IsInvariant K V p F :=
  hF.isInvariant K V p

end

end AffineGaussianInvariant.InvariantTheory.MixedTensor
