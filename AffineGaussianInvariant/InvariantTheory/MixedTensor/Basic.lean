import Mathlib

set_option autoImplicit false

namespace AffineGaussianInvariant.InvariantTheory.MixedTensor

/-- Coordinate indices for a tensor of order `d` on `𝕜^r`. -/
abbrev TensorIndex (r d : ℕ) := Fin d → Fin r

/-- Coordinate model for the `d`th tensor power of `𝕜^r`. -/
abbrev TensorCoord (𝕜 : Type*) (r d : ℕ) := TensorIndex r d → 𝕜

section Basis

variable {𝕜 : Type*} [Semiring 𝕜]
variable {r d : ℕ}

/-- The coordinate basis tensor supported at a single tensor index. -/
def basisTensor (a : TensorIndex r d) : TensorCoord 𝕜 r d :=
  fun b => if b = a then 1 else 0

@[simp]
theorem basisTensor_apply (a b : TensorIndex r d) :
    basisTensor (𝕜 := 𝕜) a b = if b = a then 1 else 0 :=
  rfl

@[simp]
theorem basisTensor_apply_self (a : TensorIndex r d) :
    basisTensor (𝕜 := 𝕜) a a = 1 := by
  simp [basisTensor]

end Basis

section Permutation

variable {𝕜 : Type*} [Semiring 𝕜]
variable {r d : ℕ}

/-- Permute tensor slots.  The convention is pullback of coordinates. -/
def permuteLinear (σ : Equiv.Perm (Fin d)) :
    TensorCoord 𝕜 r d →ₗ[𝕜] TensorCoord 𝕜 r d where
  toFun x a := x (a ∘ σ)
  map_add' x y := by
    funext a
    rfl
  map_smul' c x := by
    funext a
    rfl

@[simp]
theorem permuteLinear_apply (σ : Equiv.Perm (Fin d))
    (x : TensorCoord 𝕜 r d) (a : TensorIndex r d) :
    permuteLinear (𝕜 := 𝕜) σ x a = x (a ∘ σ) :=
  rfl

@[simp]
theorem permuteLinear_refl :
    permuteLinear (𝕜 := 𝕜) (Equiv.refl (Fin d)) = LinearMap.id := by
  ext x a
  rfl

end Permutation

section Kernel

variable {𝕜 : Type*} [CommSemiring 𝕜]
variable {r d : ℕ}

/-- Coordinate kernel of an endomorphism of a tensor power. -/
abbrev Kernel (𝕜 : Type*) (r d : ℕ) :=
  TensorIndex r d → TensorIndex r d → 𝕜

/-- Convert a finite coordinate kernel to a linear endomorphism. -/
def kernelToLinearMap (K : Kernel 𝕜 r d) :
    TensorCoord 𝕜 r d →ₗ[𝕜] TensorCoord 𝕜 r d where
  toFun x a := ∑ b, K a b * x b
  map_add' x y := by
    funext a
    simp [mul_add, Finset.sum_add_distrib]
  map_smul' c x := by
    funext a
    simp [mul_assoc, mul_left_comm, Finset.mul_sum]

/-- Kernel of a place permutation. -/
def permutationKernel (σ : Equiv.Perm (Fin d)) : Kernel 𝕜 r d :=
  fun a b => if b = a ∘ σ then 1 else 0

@[simp]
theorem kernelToLinearMap_permutationKernel (σ : Equiv.Perm (Fin d)) :
    kernelToLinearMap (permutationKernel (𝕜 := 𝕜) (r := r) σ) =
      permuteLinear (𝕜 := 𝕜) σ := by
  ext x a
  simp [kernelToLinearMap, permutationKernel]

end Kernel

end AffineGaussianInvariant.InvariantTheory.MixedTensor
