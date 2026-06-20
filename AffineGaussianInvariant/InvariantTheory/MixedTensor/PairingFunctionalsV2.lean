import Mathlib

set_option autoImplicit false

namespace AffineGaussianInvariant.InvariantTheory.MixedTensor

universe u v

/-- Ordered primal inputs. -/
abbrev PrimalTuple (V : Type v) (p : ℕ) := Fin p → V

/-- Ordered dual inputs. -/
abbrev DualTuple (K : Type u) [Semiring K]
    (V : Type v) [AddCommMonoid V] [Module K V] (p : ℕ) :=
  Fin p → Module.Dual K V

/-- Scalar-valued functions on balanced mixed inputs of bidegree `(p,p)`. -/
abbrev Functional (K : Type u) [Semiring K]
    (V : Type v) [AddCommMonoid V] [Module K V] (p : ℕ) :=
  PrimalTuple V p → DualTuple K V p → K

section

variable (K : Type u) [Field K]
variable (V : Type v) [AddCommGroup V] [Module K V]
variable (p : ℕ)

/-- Diagonal action of a linear equivalence on primal slots. -/
def actPrimal (g : V ≃ₗ[K] V) (x : PrimalTuple V p) : PrimalTuple V p :=
  fun i => g (x i)

/-- Contragredient action on dual slots. -/
def actDual (g : V ≃ₗ[K] V) (φ : DualTuple K V p) : DualTuple K V p :=
  fun i => (φ i).comp g.symm.toLinearMap

@[simp]
theorem actDual_apply (g : V ≃ₗ[K] V) (φ : DualTuple K V p)
    (i : Fin p) (x : V) :
    actDual K V p g φ i x = φ i (g.symm x) :=
  rfl

/-- Complete contraction associated with a permutation of dual slots. -/
def completeContraction (σ : Equiv.Perm (Fin p)) : Functional K V p :=
  fun x φ => ∏ i, φ (σ i) (x i)

/-- Every complete contraction is invariant under the full general linear group. -/
theorem completeContraction_invariant (σ : Equiv.Perm (Fin p))
    (g : V ≃ₗ[K] V) (x : PrimalTuple V p) (φ : DualTuple K V p) :
    completeContraction K V p σ (actPrimal K V p g x) (actDual K V p g φ) =
      completeContraction K V p σ x φ := by
  classical
  simp [completeContraction, actPrimal, actDual]

/-- Finite linear combinations of complete contractions. -/
abbrev PairingCombination := Equiv.Perm (Fin p) →₀ K

/-- Evaluation of a finite pairing combination. -/
def PairingCombination.eval (c : PairingCombination K p) : Functional K V p :=
  fun x φ => c.sum fun σ a => a * completeContraction K V p σ x φ

/-- Invariance predicate for scalar-valued mixed-tensor functionals. -/
def IsInvariant (F : Functional K V p) : Prop :=
  ∀ (g : V ≃ₗ[K] V) (x : PrimalTuple V p) (φ : DualTuple K V p),
    F (actPrimal K V p g x) (actDual K V p g φ) = F x φ

/-- Every finite linear combination of pairing contractions is invariant. -/
theorem pairingCombination_invariant (c : PairingCombination K p) :
    IsInvariant K V p (c.eval K V p) := by
  intro g x φ
  classical
  simp [PairingCombination.eval, completeContraction_invariant]

/-- A functional is pairing-generated when represented by a finite contraction combination. -/
def IsPairingGenerated (F : Functional K V p) : Prop :=
  ∃ c : PairingCombination K p, ∀ x φ, F x φ = c.eval K V p x φ

/-- Pairing-generated functionals are invariant. -/
theorem IsPairingGenerated.isInvariant {F : Functional K V p}
    (hF : IsPairingGenerated K V p F) : IsInvariant K V p F := by
  obtain ⟨c, hc⟩ := hF
  intro g x φ
  calc
    F (actPrimal K V p g x) (actDual K V p g φ) =
        c.eval K V p (actPrimal K V p g x) (actDual K V p g φ) := hc _ _
    _ = c.eval K V p x φ := pairingCombination_invariant K V p c g x φ
    _ = F x φ := (hc _ _).symm

end

end AffineGaussianInvariant.InvariantTheory.MixedTensor
