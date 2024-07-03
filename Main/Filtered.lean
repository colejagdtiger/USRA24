import Mathlib.Algebra.Algebra.Basic
import Mathlib.Order.SuccPred.Basic
import Mathlib.LinearAlgebra.Quotient
import Mathlib.Algebra.DirectSum.Basic

universe u v w

open scoped DirectSum

variable {R : Type u} {A : Type v} {ι : Type w}
[CommRing R] [Ring A] [Algebra R A] [OrderedAddCommMonoid ι] [PredOrder ι] [DecidableEq ι]
--[d : (i : ι) → Decidable (IsMin i)]
-- PredOrder instance is not the same order, need to fix

class FilteredAlgebra (𝓐 : ι → Submodule R A) where
  whole : iSup 𝓐 = ⊤
  mono : ∀ i j, i ≤ j → 𝓐 i ≤ 𝓐 j
  mul_compat : ∀ i j : ι, ∀ x y : A, x ∈ 𝓐 i → y ∈ 𝓐 j → x * y ∈ 𝓐 (i + j)
  one : 1 ∈ 𝓐 0

namespace FilteredAlgebra


def aux (𝓐 : ι → Submodule R A) (i : ι) [FilteredAlgebra 𝓐] : Submodule R A :=
  match decEq i (Order.pred i) with
  | isTrue _ => ⊥
  | isFalse _ => 𝓐 i

def gradedObject (𝓐 : ι → Submodule R A) (i : ι) [FilteredAlgebra 𝓐] :=
  Submodule.map (aux 𝓐 i).mkQ <| 𝓐 i

def gradedObject.mk (𝓐 : ι → Submodule R A) (i : ι) [FilteredAlgebra 𝓐] : 𝓐 i →ₗ[R] gradedObject 𝓐 i :=
  LinearMap.submoduleMap (aux 𝓐 i).mkQ <| 𝓐 i

def gradedObject.mk_surjective (𝓐 : ι → Submodule R A) (i : ι) [FilteredAlgebra 𝓐] :
  Function.Surjective (gradedObject.mk 𝓐 i) := LinearMap.submoduleMap_surjective (aux 𝓐 i).mkQ <| 𝓐 i


def gradedObject.prod (𝓐 : ι → Submodule R A) (i j : ι) [FilteredAlgebra 𝓐] :
  gradedObject 𝓐 i → gradedObject 𝓐 j → gradedObject 𝓐 (i + j) := by
    intro x y
    let f := gradedObject.mk_surjective 𝓐 _ x
    have x := f
    --rintro ⟨x,h₁⟩ ⟨y,h₂⟩

    --let f := Quotient.lift₂ (fun x y : A => Quotient.mk _)
    --let g := Quotient.map₂ <| mul 𝓐
    sorry

end FilteredAlgebra


namespace assocGraded

def assocGraded (𝓐 : ι → Submodule R A) [FilteredAlgebra 𝓐] :=
   ⨁ i : ι, FilteredAlgebra.gradedObject 𝓐 i

end assocGraded
