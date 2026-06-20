import AffineGaussianInvariant.InvariantTheory.MixedTensor.S6_3Target

set_option autoImplicit false

namespace AffineGaussianInvariant.InvariantTheory.MixedTensor

universe u v

section

variable (K : Type u) [Field K]
variable (V : Type v) [AddCommGroup V] [Module K V]

/-- The balanced mixed-tensor FFT is trivial in bidegree `(0,0)`. -/
theorem fftStatement_zero : FFTStatement K V 0 := by
  intro F hmulti hinv
  classical
  let x0 : PrimalTuple V 0 := fun i => Fin.elim0 i
  let φ0 : DualTuple K V 0 := fun i => Fin.elim0 i
  let σ0 : Equiv.Perm (Fin 0) := Equiv.refl (Fin 0)
  let c : PairingCombination K 0 := Finsupp.single σ0 (F x0 φ0)
  refine ⟨c, ?_⟩
  intro x φ
  have hx : x = x0 := Subsingleton.elim _ _
  have hφ : φ = φ0 := Subsingleton.elim _ _
  subst x
  subst φ
  simp [PairingCombination.eval, completeContraction, c, σ0]

/-- Consequently the concrete S6.3 target is closed at degree zero. -/
theorem concreteS6_3_zero (r : ℕ) : ConcreteS6_3 r 0 :=
  fftStatement_zero ℂ (Fin r → ℂ)

end

end AffineGaussianInvariant.InvariantTheory.MixedTensor
