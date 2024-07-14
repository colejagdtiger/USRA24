import Mathlib.Order.SuccPred.Basic
import Mathlib.LinearAlgebra.Quotient
import Mathlib.Algebra.DirectSum.Basic
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.RingTheory.GradedAlgebra.Basic

universe u v w

open scoped DirectSum



variable {R : Type u} {M : Type v} {ι : Type w}
[CommRing R] [AddCommGroup M] [Module R M] [OrderedAddCommMonoid ι] [PredOrder ι] [DecidableEq ι]
-- should change the PredOrder stuff maybe?

class FilteredModule (𝓜 : ι → Submodule R M) where
  whole : iSup 𝓜 = ⊤
  mono : Monotone 𝓜

namespace FilteredModule

def aux (𝓜 : ι → Submodule R M) (i : ι) [FilteredModule 𝓜] : Submodule R M :=
  match decEq i (Order.pred i) with
  | isTrue _ => ⊥
  | isFalse _ => 𝓜 (Order.pred i)

lemma aux_le (𝓜 : ι → Submodule R M) [FilteredModule 𝓜] : ∀ i, aux 𝓜 i ≤ 𝓜 i := fun i =>
  match decEq i (Order.pred i) with
  | isTrue _ => by
    dsimp [aux]
    split
    · exact bot_le
    · apply mono
      exact Order.pred_le i
  | isFalse _ => by
    dsimp [aux]
    split
    · exact bot_le
    · apply mono
      exact Order.pred_le i


def gradedObject' (𝓜 : ι → Submodule R M) (i : ι) [FilteredModule 𝓜] : sorry := by
  let X := 𝓜 i
  let Y := aux 𝓜 i
  let h := aux_le 𝓜 i
  --let Q := X ⧸
  --letI := (𝓜 i) ⧸ (aux 𝓜 i)
  --let h := X ⧸ Y
  sorry

def gradedObject (𝓜 : ι → Submodule R M) (i : ι) [FilteredModule 𝓜] :=
  Submodule.map (aux 𝓜 i).mkQ <| 𝓜 i

def gradedObject.mk (𝓜 : ι → Submodule R M) (i : ι) [FilteredModule 𝓜] :
  𝓜 i →ₗ[R] gradedObject 𝓜 i :=
    LinearMap.submoduleMap (aux 𝓜 i).mkQ <| 𝓜 i

-- lemma gradedObject.mk_apply {𝓐 : ι → Submodule R A} {i : ι} [FilteredAlgebra 𝓐] (x : 𝓐 i) :
--   gradedObject 𝓐 i := by
--     let h := LinearMap.submoduleMap_coe_apply (aux 𝓐 i).mkQ x
--     sorry

lemma gradedObject.mk_surjective (𝓜 : ι → Submodule R M) (i : ι) [FilteredModule 𝓜] :
  Function.Surjective (gradedObject.mk 𝓜 i) :=
    LinearMap.submoduleMap_surjective (aux 𝓜 i).mkQ <| 𝓜 i

abbrev assocGradedModule (𝓜 : ι → Submodule R M) [FilteredModule 𝓜] :=
  ⨁ i : ι, gradedObject 𝓜 i

end FilteredModule


variable {R : Type u} {A : Type v} {ι : Type w}
[CommRing R] [Ring A] [Algebra R A] [OrderedAddCommMonoid ι] [PredOrder ι] [DecidableEq ι]

class FilteredAlgebra (𝓐 : ι → Submodule R A) extends FilteredModule 𝓐 where
  mul_compat' : ∀ i j, 𝓐 i * 𝓐 j ≤ 𝓐 (i + j)
  one' : 1 ∈ 𝓐 0

namespace FilteredAlgebra

lemma r_in_zero (𝓐 : ι → Submodule R A) [FilteredAlgebra 𝓐] (r : R) : algebraMap R A r ∈ (𝓐 0) := by
  simp only [Algebra.algebraMap_eq_smul_one]
  exact Submodule.smul_mem (𝓐 0) r one'

lemma mul_compat {𝓐 : ι → Submodule R A} [FilteredAlgebra 𝓐] {i j : ι} :
  a ∈ 𝓐 i → b ∈ 𝓐 j → a * b ∈ 𝓐 (i + j) := fun h₁ h₂ =>
    mul_compat' i j <| Submodule.mul_mem_mul h₁ h₂


def hMul {𝓐 : ι → Submodule R A} [FilteredAlgebra 𝓐] {i j : ι} (x : 𝓐 i) (y : 𝓐 j) : 𝓐 (i + j) :=
    ⟨↑x * ↑y, mul_compat (Submodule.coe_mem x) (Submodule.coe_mem y)⟩

@[simp]
lemma coe_hMul {𝓐 : ι → Submodule R A} [FilteredAlgebra 𝓐] {i j : ι} (x : 𝓐 i) (y : 𝓐 j) :
  ↑(hMul x y) = (x : A) * y := rfl

-- lemma hMul_assoc {𝓐 : ι → Submodule R A} [FilteredAlgebra 𝓐] {i j k : ι} (x : 𝓐 i) (y : 𝓐 j) (z : 𝓐 k) :
--   hMul (hMul x y) z = hMul x (hMul y z) := rfl

@[simp]
lemma smul_assoc_hMul {𝓐 : ι → Submodule R A} [FilteredAlgebra 𝓐] {i j : ι} (r : R) (x : 𝓐 i) (y : 𝓐 j) :
   hMul x (r • y) = hMul (r • x) y := by
    apply sub_eq_zero.1
    apply Submodule.coe_eq_zero.1
    simp only [AddSubgroupClass.coe_sub, coe_hMul, SetLike.val_smul, Algebra.smul_mul_assoc,
      Algebra.mul_smul_comm, sub_self]

@[simp]
lemma smul_comm_hMul {𝓐 : ι → Submodule R A} [FilteredAlgebra 𝓐] {i j : ι} (r : R) (x : 𝓐 i) (y : 𝓐 j) :
  hMul (r • x) y = r • hMul x y := by
    apply sub_eq_zero.1
    apply Submodule.coe_eq_zero.1
    simp only [AddSubgroupClass.coe_sub, coe_hMul, SetLike.val_smul, Algebra.smul_mul_assoc,
      sub_self]

@[simp]
lemma hMul_lDistrib {𝓐 : ι → Submodule R A} [FilteredAlgebra 𝓐] {i j : ι} (x : 𝓐 i) (y₁ y₂ : 𝓐 j) :
  hMul x (y₁ + y₂) = hMul x y₁ + hMul x y₂ := by
    apply sub_eq_zero.1
    apply Submodule.coe_eq_zero.1
    simp only [AddSubgroupClass.coe_sub, coe_hMul, AddSubmonoid.coe_add, Distrib.left_distrib,
      Submodule.coe_toAddSubmonoid, sub_self]

@[simp]
lemma hMul_rDistrib {𝓐 : ι → Submodule R A} [FilteredAlgebra 𝓐] {i j : ι} (x₁ x₂ : 𝓐 i) (y : 𝓐 j) :
  hMul (x₁ + x₂) y = hMul x₁ y + hMul x₂ y := by
    apply sub_eq_zero.1
    apply Submodule.coe_eq_zero.1
    simp only [AddSubgroupClass.coe_sub, coe_hMul, AddSubmonoid.coe_add, Distrib.right_distrib,
      Submodule.coe_toAddSubmonoid, sub_self]

def hMulHom (𝓐 : ι → Submodule R A) (i j : ι) [FilteredAlgebra 𝓐] :
  𝓐 i →ₗ[R] 𝓐 j →ₗ[R] 𝓐 (i + j) where
    toFun x := {
      toFun := fun y => hMul x y
      map_add' := fun y₁ y₂ => hMul_lDistrib x y₁ y₂
      map_smul' := fun r y => by simp only [smul_assoc_hMul, smul_comm_hMul, RingHom.id_apply]
    }
    map_add' x₁ x₂ := by
      ext y
      simp only [hMul_rDistrib, LinearMap.coe_mk, AddHom.coe_mk, AddSubmonoid.coe_add,
        Submodule.coe_toAddSubmonoid, coe_hMul, LinearMap.add_apply]
    map_smul' r x := by
      ext y
      simp only [smul_comm_hMul, LinearMap.coe_mk, AddHom.coe_mk, SetLike.val_smul, coe_hMul,
        RingHom.id_apply, LinearMap.smul_apply]

abbrev gradedObject (𝓐 : ι → Submodule R A) (i : ι) [FilteredAlgebra 𝓐] :=
  FilteredModule.gradedObject 𝓐 i

def gHMul {𝓐 : ι → Submodule R A} {i j : ι} [FilteredAlgebra 𝓐] :
  𝓐 i → 𝓐 j → FilteredModule.gradedObject 𝓐 (i + j) := fun x y =>
    FilteredModule.gradedObject.mk _ _ (hMul x y)


def gHMulHom (𝓐 : ι → Submodule R A) (i j : ι) [FilteredAlgebra 𝓐] :
  𝓐 i →ₗ[R] 𝓐 j →ₗ[R] FilteredModule.gradedObject 𝓐 (i + j) :=
     LinearMap.compr₂ (hMulHom 𝓐 i j) (FilteredModule.gradedObject.mk 𝓐 (i + j))

#check Submodule.mapQLinear
def foo (𝓐 : ι → Submodule R A) (i j : ι) [FilteredAlgebra 𝓐] :
  LinearMap.ker (FilteredModule.gradedObject.mk 𝓐 i) ≤ LinearMap.ker (gHMulHom 𝓐 i j) := by
    intro x hx
    sorry

def prod₁ (𝓐 : ι → Submodule R A) (i j : ι) [FilteredAlgebra 𝓐] :
  gradedObject 𝓐 i →ₗ[R] 𝓐 j →ₗ[R] gradedObject 𝓐 (i + j) := by
    let K := LinearMap.ker (gHMulHom 𝓐 i j)
    let G := LinearMap.ker (FilteredModule.gradedObject.mk 𝓐 i)
    let h : G ≤ K := sorry
    sorry

def prod₂ (𝓐 : ι → Submodule R A) (i j : ι) [FilteredAlgebra 𝓐] :
  𝓐 i →ₗ[R] gradedObject 𝓐 j →ₗ[R] gradedObject 𝓐 (i + j) := sorry


def prod (𝓐 : ι → Submodule R A) (i j : ι) [FilteredAlgebra 𝓐] :
  gradedObject 𝓐 i →ₗ[R] gradedObject 𝓐 j →ₗ[R] gradedObject 𝓐 (i + j) := by

    sorry

def instSubAlgebraZero (𝓐 : ι → Submodule R A) [FilteredAlgebra 𝓐] : Subalgebra R A where
  carrier := 𝓐 0
  mul_mem' a b := by
    let h := mul_compat a b
    simp only [add_zero] at h
    exact h
  add_mem' := Submodule.add_mem (𝓐 0)
  algebraMap_mem' r := (r_in_zero 𝓐 r)


-- As written this is not true
instance instGradedAlgebra (𝓐 : ι → Submodule R A) [GradedAlgebra 𝓐] : FilteredAlgebra 𝓐 where
  whole := by
    sorry
  mono := sorry
  mul_compat' := sorry
  one' := sorry


end FilteredAlgebra
