import Mathlib.Algebra.Algebra.Subalgebra.Basic

universe u v w

variable {R : Type u} {M : Type v} {ι : Type w}
[CommRing R] [AddCommGroup M] [Module R M] [OrderedAddCommMonoid ι]

class FilteredModule (𝓜 : ι → Submodule R M) where
  whole : iSup 𝓜 = ⊤
  mono : Monotone 𝓜

variable {R : Type u} {A : Type v} {ι : Type w}
[CommRing R] [Ring A] [Algebra R A] [OrderedAddCommMonoid ι]

class FilteredAlgebra (𝓐 : ι → Submodule R A) extends FilteredModule 𝓐 where
  mul_compat' : ∀ i j, 𝓐 i * 𝓐 j ≤ 𝓐 (i + j)
  one' : 1 ∈ 𝓐 0

namespace FilteredAlgebra

lemma r_in_zero (𝓐 : ι → Submodule R A) [FilteredAlgebra 𝓐] (r : R) : algebraMap R A r ∈ (𝓐 0) := by
    simp only [Algebra.algebraMap_eq_smul_one]
    exact Submodule.smul_mem (𝓐 0) r one'

lemma mul_compat {𝓐 : ι → Submodule R A} [FilteredAlgebra 𝓐] :
  ∀ i j, a ∈ 𝓐 i → b ∈ 𝓐 j → a * b ∈ 𝓐 (i + j) := fun i j h₁ h₂ =>
    mul_compat' i j <| Submodule.mul_mem_mul h₁ h₂

def instSubAlgebraZero (𝓐 : ι → Submodule R A) [FilteredAlgebra 𝓐] : Subalgebra R A where
  carrier := 𝓐 0
  mul_mem' a b := by
    let h := mul_compat 0 0 a b
    simp only [add_zero] at h
    exact h
  add_mem' := Submodule.add_mem (𝓐 0)
  algebraMap_mem' r := (r_in_zero 𝓐 r)

end FilteredAlgebra
