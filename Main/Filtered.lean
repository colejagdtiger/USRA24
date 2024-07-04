import Mathlib.Algebra.Algebra.Basic
import Mathlib.Order.SuccPred.Basic
import Mathlib.LinearAlgebra.Quotient
import Mathlib.Algebra.DirectSum.Basic
import Mathlib.Algebra.Algebra.Operations

universe u v w

open scoped DirectSum


variable {R : Type u} {A : Type v} {ι : Type w}
[CommRing R] [Ring A] [Algebra R A] [OrderedAddCommMonoid ι] [PredOrder ι] [DecidableEq ι]


class FilteredAlgebra (𝓐 : ι → Submodule R A) where
  whole : iSup 𝓐 = ⊤
  mono : Monotone 𝓐 --∀ i j, i ≤ j → 𝓐 i ≤ 𝓐 j
  mul_compat : ∀ i j, 𝓐 i * 𝓐 j ≤ 𝓐 (i + j)
  one : 1 ∈ 𝓐 0

namespace FilteredAlgebra

instance instZeroInhabited (𝓐 : ι → Submodule R A) [FilteredAlgebra 𝓐] : Inhabited (𝓐 0) :=
  inferInstance

instance instZeroSemiring (𝓐 : ι → Submodule R A) [FilteredAlgebra 𝓐] : Semiring (𝓐 0) := sorry

instance instZeroAlgebra (𝓐 : ι → Submodule R A) [FilteredAlgebra 𝓐] : Algebra R (𝓐 0) := sorry

--def zero_hom (𝓐 : ι → Submodule R A) : 𝓐 0 →+* A := sorry

--gradedAlgebra is instance of filtered

-- mul_compat_mem?
lemma mul_compat' (𝓐 : ι → Submodule R A) [FilteredAlgebra 𝓐] :
  ∀ i j, x ∈ 𝓐 i → y ∈ 𝓐 j → x * y ∈ 𝓐 (i + j) := fun i j h₁ h₂ =>
    mul_compat i j <| Submodule.mul_mem_mul h₁ h₂


def aux (𝓐 : ι → Submodule R A) (i : ι) [FilteredAlgebra 𝓐] : Submodule R A :=
  match decEq i (Order.pred i) with
  | isTrue _ => ⊥
  | isFalse _ => 𝓐 (Order.pred i)

lemma aux_le (𝓐 : ι → Submodule R A) [FilteredAlgebra 𝓐] : ∀ i, aux 𝓐 i ≤ 𝓐 j := fun i =>
  match decEq i (Order.pred i) with
  | isTrue _ => sorry
  | isFalse _ => by
    dsimp [aux]
    --let f : 𝓐 i ≤ 𝓐 i := mono i i
    split
    · sorry
    · sorry


def gradedObject' (𝓐 : ι → Submodule R A) (i : ι) [FilteredAlgebra 𝓐] : sorry := by
  let X := 𝓐 i
  let Y := aux 𝓐 i
  --let h := X ⧸ Y
  sorry

def gradedObject (𝓐 : ι → Submodule R A) (i : ι) [FilteredAlgebra 𝓐] :=
  Submodule.map (aux 𝓐 i).mkQ <| 𝓐 i

def gradedObject.mk (𝓐 : ι → Submodule R A) (i : ι) [FilteredAlgebra 𝓐] : 𝓐 i →ₗ[R] gradedObject 𝓐 i :=
  LinearMap.submoduleMap (aux 𝓐 i).mkQ <| 𝓐 i

-- lemma gradedObject.mk_apply {𝓐 : ι → Submodule R A} {i : ι} [FilteredAlgebra 𝓐] (x : 𝓐 i) :
--   gradedObject 𝓐 i := by
--     let h := LinearMap.submoduleMap_coe_apply (aux 𝓐 i).mkQ x
--     sorry

lemma gradedObject.mk_surjective (𝓐 : ι → Submodule R A) (i : ι) [FilteredAlgebra 𝓐] :
  Function.Surjective (gradedObject.mk 𝓐 i) := LinearMap.submoduleMap_surjective (aux 𝓐 i).mkQ <| 𝓐 i


def fee (𝓐 : ι → Submodule R A) (i j : ι) [FilteredAlgebra 𝓐] :
  𝓐 i → 𝓐 j → 𝓐 (i + j) := fun x y =>
    ⟨x * y, mul_compat' 𝓐 i j (Submodule.coe_mem x) (Submodule.coe_mem y)⟩

def foo (𝓐 : ι → Submodule R A) (i j : ι) [FilteredAlgebra 𝓐] :
  𝓐 i → 𝓐 j → gradedObject 𝓐 (i + j) := fun x y =>
    gradedObject.mk _ _ <| fee _ _ _ x y


--def compat (𝓐 : ι → Submodule R A) (i j : ι) [FilteredAlgebra 𝓐] :

def prod (𝓐 : ι → Submodule R A) (i j : ι) [FilteredAlgebra 𝓐] :
  gradedObject 𝓐 i → gradedObject 𝓐 j → gradedObject 𝓐 (i + j) := by
    let R := (Submodule.quotientRel (aux 𝓐 i))
    let S := (Submodule.quotientRel (aux 𝓐 j))
    --let h := Quotient.lift₂ (fun x y => x * y) (sorry) (A ⧸ (aux 𝓐 i))
    --let g := Quotient.map₂ <| mul 𝓐
    sorry

end FilteredAlgebra


namespace assocGraded

def assocGraded (𝓐 : ι → Submodule R A) [FilteredAlgebra 𝓐] :=
   ⨁ i : ι, FilteredAlgebra.gradedObject 𝓐 i

end assocGraded
