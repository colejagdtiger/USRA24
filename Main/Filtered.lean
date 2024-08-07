import Mathlib.Order.SuccPred.Basic
import Mathlib.LinearAlgebra.Quotient
import Mathlib.Algebra.DirectSum.Basic
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.RingTheory.GradedAlgebra.Basic
import Mathlib.Algebra.Lie.Free
import Mathlib.LinearAlgebra.TensorAlgebra.Grading

universe u v w u₁

open scoped DirectSum



variable {R : Type u} {M : Type v} {ι : Type w}
[CommRing R] [AddCommGroup M] [Module R M] [OrderedAddCommMonoid ι] [PredOrder ι] [DecidableEq ι]
-- should change the PredOrder stuff maybe?

-- better names (hausdorff?)
class FilteredModule (𝓜 : ι → Submodule R M) where
  whole : ⨆ i, 𝓜 i = ⊤
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

def aux_ι (𝓜 : ι → Submodule R M) [FilteredModule 𝓜] (i : ι) := Submodule.inclusion <| aux_le 𝓜 i

def aux_ι_map (𝓜 : ι → Submodule R M) [FilteredModule 𝓜] (i : ι) := Submodule.map (aux_ι 𝓜 i) ⊤

lemma mem_aux_iff_mem_aux_ι_map {𝓜 : ι → Submodule R M} [FilteredModule 𝓜] {i : ι} (x : 𝓜 i) :
  x ∈ aux_ι_map 𝓜 i ↔ ↑x ∈ aux 𝓜 i := sorry

abbrev gradedObject (𝓜 : ι → Submodule R M) (i : ι) [FilteredModule 𝓜] :=
  (𝓜 i) ⧸ aux_ι_map 𝓜 i

def gradedObject.mk (𝓜 : ι → Submodule R M) (i : ι) [FilteredModule 𝓜] :
  𝓜 i →ₗ[R] gradedObject 𝓜 i := Submodule.mkQ <| aux_ι_map 𝓜 i

lemma gradedObject.mk_surjective (𝓜 : ι → Submodule R M) (i : ι) [FilteredModule 𝓜] :
  Function.Surjective (gradedObject.mk 𝓜 i) :=
    Submodule.mkQ_surjective <| aux_ι_map 𝓜 i

def gradedObject' (𝓜 : ι → Submodule R M) (i : ι) [FilteredModule 𝓜] :=
  Submodule.map (aux 𝓜 i).mkQ <| 𝓜 i

def gradedObject'.mk (𝓜 : ι → Submodule R M) (i : ι) [FilteredModule 𝓜] :
  𝓜 i →ₗ[R] gradedObject' 𝓜 i := LinearMap.submoduleMap (aux 𝓜 i).mkQ <| 𝓜 i

lemma gradedObject'.mk_surjective (𝓜 : ι → Submodule R M) (i : ι) [FilteredModule 𝓜] :
  Function.Surjective (gradedObject'.mk 𝓜 i) :=
    LinearMap.submoduleMap_surjective (aux 𝓜 i).mkQ <| 𝓜 i

abbrev assocGradedModule (𝓜 : ι → Submodule R M) [FilteredModule 𝓜] :=
  ⨁ i : ι, gradedObject 𝓜 i

-- Function.Surjective.FilteredAlgebra
instance instPushforwardOfFiltered (𝓜 : ι → Submodule R M) [FilteredModule 𝓜] {N : Type w}
  [AddCommGroup N] [Module R N]
  (f : M →ₗ[R] N) (h : Function.Surjective f) : FilteredModule <| (Submodule.map f).comp 𝓜 where
    whole := by
      simp only [Function.comp_apply, ← Submodule.map_iSup, whole, Submodule.map_top,
        LinearMap.range_eq_top, h]
    mono _ _ h := Submodule.map_mono <| mono h

--def ofGraded (𝓜 : ι → Submodule R M) [GradedModule 𝓜]


end FilteredModule


variable {R : Type u} {A : Type v} {ι : Type w}
[CommRing R] [Ring A] [Algebra R A] [OrderedAddCommMonoid ι] [PredOrder ι] [DecidableEq ι]

class FilteredAlgebra (𝓐 : ι → Submodule R A) extends FilteredModule 𝓐 where
  mul_compat' : ∀ ⦃i j : ι⦄, 𝓐 i * 𝓐 j ≤ 𝓐 (i + j)
  one' : 1 ∈ 𝓐 0

namespace FilteredAlgebra

lemma r_in_zero (𝓐 : ι → Submodule R A) [FilteredAlgebra 𝓐] (r : R) : algebraMap R A r ∈ (𝓐 0) := by
  simp only [Algebra.algebraMap_eq_smul_one]
  exact Submodule.smul_mem (𝓐 0) r one'

lemma mul_compat {𝓐 : ι → Submodule R A} [FilteredAlgebra 𝓐] {i j : ι} :
  a ∈ 𝓐 i → b ∈ 𝓐 j → a * b ∈ 𝓐 (i + j) := fun h₁ h₂ =>
    mul_compat' <| Submodule.mul_mem_mul h₁ h₂


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

abbrev aux (𝓐 : ι → Submodule R A) (i : ι) [FilteredAlgebra 𝓐] :=
  FilteredModule.aux 𝓐 i

abbrev aux_ι (𝓐 : ι → Submodule R A) (i : ι) [FilteredAlgebra 𝓐] :=
  FilteredModule.aux_ι 𝓐 i

abbrev aux_ι_map (𝓐 : ι → Submodule R A) (i : ι) [FilteredAlgebra 𝓐] :=
  FilteredModule.aux_ι_map 𝓐 i

abbrev gradedObject (𝓐 : ι → Submodule R A) (i : ι) [FilteredAlgebra 𝓐] :=
  FilteredModule.gradedObject 𝓐 i

abbrev assocGradedAlgebra (𝓐 : ι → Submodule R A) [FilteredAlgebra 𝓐] :=
  FilteredModule.assocGradedModule 𝓐

def gHMulHom (𝓐 : ι → Submodule R A) (i j : ι) [FilteredAlgebra 𝓐] :
  𝓐 i →ₗ[R] 𝓐 j →ₗ[R] FilteredModule.gradedObject 𝓐 (i + j) :=
     LinearMap.compr₂ (hMulHom 𝓐 i j) (FilteredModule.gradedObject.mk 𝓐 (i + j))

-- wrong name
def gHMulHom_apply {𝓐 : ι → Submodule R A} {i j : ι} [FilteredAlgebra 𝓐] (x : 𝓐 i) (y : 𝓐 j) :=
  gHMulHom 𝓐 i j x y

lemma gHMulHom_aux_zero {𝓐 : ι → Submodule R A} {i : ι} [FilteredAlgebra 𝓐] (x : 𝓐 i)
  (h : x ∈ FilteredModule.aux_ι_map 𝓐 i) : ∀ j, ∀ y : 𝓐 j, gHMulHom 𝓐 i j x y = 0 := by
    let y := (x : A)

    sorry

-- #check Submodule.mapQLinear
-- def foo (𝓐 : ι → Submodule R A) (i j : ι) [FilteredAlgebra 𝓐] :
--   LinearMap.ker (FilteredModule.gradedObject.mk 𝓐 i) ≤ LinearMap.ker (gHMulHom 𝓐 i j) := by
--     intro x hx
--     sorry

def lift₁ (𝓐 : ι → Submodule R A) (i j : ι) [FilteredAlgebra 𝓐] :
  gradedObject 𝓐 i →ₗ[R] 𝓐 j →ₗ[R] gradedObject 𝓐 (i + j) := by
    let h : aux_ι_map 𝓐 i ≤ LinearMap.ker (gHMulHom 𝓐 i j) := by
      intro x h
      simp only [LinearMap.mem_ker]
      ext y
      dsimp [gHMulHom, hMulHom, hMul]
      sorry
    exact Submodule.liftQ (aux_ι_map 𝓐 i) (gHMulHom 𝓐 i j) h

def lift₂ (𝓐 : ι → Submodule R A) (i j : ι) [FilteredAlgebra 𝓐] :
  𝓐 i →ₗ[R] gradedObject 𝓐 j →ₗ[R] gradedObject 𝓐 (i + j) := by
    rw [add_comm]
    exact LinearMap.flip <| lift₁ 𝓐 j i


--def lift (𝓐 : ι → Submodule R A) (i j : ι) [FilteredAlgebra 𝓐]
  --: ∀ (x₁ : 𝓐 i) (y₁ : 𝓐 j) (x₂ : 𝓐 i) (y₂ : 𝓐 j), x₁ ≈ x₂ → y₁ ≈ y₂ → f a₁ b₁ = f a₂ b₂

def lift (𝓐 : ι → Submodule R A) (i j : ι) [FilteredAlgebra 𝓐] :
  gradedObject 𝓐 i →ₗ[R] gradedObject 𝓐 j →ₗ[R] gradedObject 𝓐 (i + j) := by
    let h : aux_ι_map 𝓐 i ≤ LinearMap.ker (lift₂ 𝓐 i j) :=
      sorry
    exact Submodule.liftQ (aux_ι_map 𝓐 i) (lift₂ 𝓐 i j) h

--instance instAssocGradedIsAlgebra (𝓐 : ι → Submodule R A) [FilteredAlgebra 𝓐] : Algebra R

def instSubAlgebraZero (𝓐 : ι → Submodule R A) [FilteredAlgebra 𝓐] : Subalgebra R A where
  carrier := 𝓐 0
  mul_mem' a b := by
    let h := mul_compat a b
    simp only [add_zero] at h
    exact h
  add_mem' := Submodule.add_mem (𝓐 0)
  algebraMap_mem' r := (r_in_zero 𝓐 r)


abbrev assocGAlgebra (𝓐 : ι → Submodule R A) [FilteredAlgebra 𝓐] := fun i : ι => gradedObject 𝓐 i

instance instGMul (𝓐 : ι → Submodule R A) [FilteredAlgebra 𝓐] : GradedMonoid.GMul (assocGAlgebra 𝓐) where
  mul x y := lift 𝓐 _ _ x y

instance instGOne (𝓐 : ι → Submodule R A) [FilteredAlgebra 𝓐] : GradedMonoid.GOne (assocGAlgebra 𝓐) where
  one := FilteredModule.gradedObject.mk 𝓐 0 (1 : instSubAlgebraZero 𝓐)

@[simp]
lemma gMul_zero (𝓐 : ι → Submodule R A) [FilteredAlgebra 𝓐] : ∀ {i j : ι} (x : assocGAlgebra 𝓐 i),
  GradedMonoid.GMul.mul x (0 : assocGAlgebra 𝓐 j) = 0 := fun x =>
    sorry

@[simp]
lemma zero_gMul (𝓐 : ι → Submodule R A) [FilteredAlgebra 𝓐] : ∀ {i j : ι} (y : assocGAlgebra 𝓐 j),
  GradedMonoid.GMul.mul (0 : assocGAlgebra 𝓐 i) y = 0 := fun y => sorry

lemma gMul_add (𝓐 : ι → Submodule R A) [FilteredAlgebra 𝓐] : ∀ {i j : ι} (x : assocGAlgebra 𝓐 i)
  (y₁ y₂ : assocGAlgebra 𝓐 j),
  GradedMonoid.GMul.mul x (y₁ + y₂) = GradedMonoid.GMul.mul x y₁ + GradedMonoid.GMul.mul x y₂ := sorry

lemma add_gMul (𝓐 : ι → Submodule R A) [FilteredAlgebra 𝓐] : ∀ {i j : ι} (x₁ x₂ : assocGAlgebra 𝓐 i)
  (y : assocGAlgebra 𝓐 j),
  GradedMonoid.GMul.mul (x₁ + x₂) y = GradedMonoid.GMul.mul x₁ y + GradedMonoid.GMul.mul x₂ y := sorry

lemma one_gMul (𝓐 : ι → Submodule R A) [FilteredAlgebra 𝓐] :
  ∀ (x : GradedMonoid (assocGAlgebra 𝓐)), 1 * x = x := fun x =>
    sorry

lemma gMul_one (𝓐 : ι → Submodule R A) [FilteredAlgebra 𝓐] :
  ∀ (x : GradedMonoid (assocGAlgebra 𝓐)), x * 1 = x := fun x =>
    sorry

lemma mul_assoc (𝓐 : ι → Submodule R A) [FilteredAlgebra 𝓐] :
  ∀ (x y z : GradedMonoid (assocGAlgebra 𝓐)), x * y * z = x * (y * z) := fun x y z =>
    sorry


def natCast (𝓐 : ι → Submodule R A) [FilteredAlgebra 𝓐] : ℕ → assocGAlgebra 𝓐 0 :=
  fun n => FilteredModule.gradedObject.mk 𝓐 0 (n : instSubAlgebraZero 𝓐)

lemma natCast_zero (𝓐 : ι → Submodule R A) [FilteredAlgebra 𝓐] : natCast 𝓐 0 = 0 := by
  dsimp [natCast]
  simp only [Nat.cast_zero, map_zero]

lemma natCast_succ (𝓐 : ι → Submodule R A) [FilteredAlgebra 𝓐] :
  ∀ n, natCast 𝓐 (n + 1) = natCast 𝓐 n + GradedMonoid.GOne.one := fun n => by
  dsimp [natCast, GradedMonoid.GOne.one]
  simp only [Nat.cast_add, Nat.cast_one, map_add]


instance instGSemiring (𝓐 : ι → Submodule R A) [FilteredAlgebra 𝓐] :
  DirectSum.GSemiring (assocGAlgebra 𝓐) where
    mul_zero := gMul_zero 𝓐
    zero_mul := zero_gMul 𝓐
    mul_add := gMul_add 𝓐
    add_mul := add_gMul 𝓐
    one_mul := one_gMul 𝓐
    mul_one := gMul_one 𝓐
    mul_assoc := mul_assoc 𝓐
    natCast := natCast 𝓐
    natCast_zero := natCast_zero 𝓐
    natCast_succ := natCast_succ 𝓐

def toFun (𝓐 : ι → Submodule R A) [FilteredAlgebra 𝓐] : R →+ assocGAlgebra 𝓐 0 :=
  (FilteredModule.gradedObject.mk 𝓐 0).toAddMonoidHom.comp
    (algebraMap R (instSubAlgebraZero 𝓐)).toAddMonoidHom

instance gradedAlg (𝓐 : ι → Submodule R A) [FilteredAlgebra 𝓐] :
  DirectSum.GAlgebra R (assocGAlgebra 𝓐) where
    toFun := toFun 𝓐
    map_one := by
      dsimp [toFun, GradedMonoid.GOne.one]
      erw [RingHom.map_one (algebraMap R (instSubAlgebraZero 𝓐))]
    map_mul r s :=

      sorry
    commutes := sorry
    smul_def :=
      sorry



abbrev ofGraded (𝓐 : ι → Submodule R A) [GradedAlgebra 𝓐] : ι → Submodule R A := fun i =>
  ⨆ j : {j : ι | j ≤ i }, 𝓐 j


lemma ofGraded.le_incl (𝓐 : ι → Submodule R A) [GradedAlgebra 𝓐] :
  ∀ i j, i ≤ j → 𝓐 i ≤ ofGraded 𝓐 j := fun i j h => by
    letI := le_iSup (fun t : {i : ι | i ≤ j } => 𝓐 t)
    simp only [Set.coe_setOf, Set.mem_setOf_eq, Subtype.forall] at this
    exact this i h


lemma ofGraded.mono (𝓐 : ι → Submodule R A) [GradedAlgebra 𝓐] : Monotone (ofGraded 𝓐) := by
  intro i j h
  simp only [iSup_le_iff, Set.coe_setOf, Set.mem_setOf_eq, Subtype.forall]
  intro k h'
  exact ofGraded.le_incl 𝓐 k j (h'.trans h)


-- As written this is not true
instance instGradedIsFiltered (𝓐 : ι → Submodule R A) [GradedAlgebra 𝓐] : FilteredAlgebra (ofGraded 𝓐) where
  whole := by
    rw [Submodule.eq_top_iff']
    intro x
    --let h : ∀ i, 𝓐 i ≤ ofGraded 𝓐 i := fun i => ofGraded.le_incl 𝓐 i i (le_refl i)
    letI := iSup_mono (fun i => ofGraded.le_incl 𝓐 i i (le_refl i))
    apply this
    let h : iSup 𝓐 = ⊤ :=

      sorry
    simp only [h, Submodule.mem_top]
  mono := ofGraded.mono 𝓐
  one' := by
    letI := ofGraded.le_incl 𝓐 0 0 (le_refl 0)
    apply this

    sorry
  mul_compat' i j := by

    sorry


-- show the assocGAlg of a graded alg is the OG alg


-- def instPullbackOfFiltered (𝓐 : ι → Submodule R A) [FilteredAlgebra 𝓐] {B : Type w} [Ring B] (f : A →+*ₗ[R] B) :
--   sorry := by
--     sorry

-- Function.Surjective.FilteredAlgebra
instance instPushforwardOfFiltered (𝓐 : ι → Submodule R A) [FilteredAlgebra 𝓐] {B : Type u₁} [Ring B] [Algebra R B]
  (f : A →ₐ[R] B) (h : Function.Surjective f) : FilteredAlgebra <| (Submodule.map f.toLinearMap).comp 𝓐 where
    whole := by
      simp only [Function.comp_apply, ← Submodule.map_iSup, FilteredModule.whole, Submodule.map_top,
        LinearMap.range_eq_top]
      intro X
      exact h X
    mono _ _ h := Submodule.map_mono <| FilteredModule.mono h
    one' := by
      simp only [Function.comp_apply, Submodule.mem_map]
      exact ⟨1, one', map_one f⟩
    mul_compat' _ _ := by
      simp only [Function.comp_apply, ← Submodule.map_mul]
      apply Submodule.map_mono
      simp only [FilteredAlgebra.mul_compat']


def objectHom {𝓐 : ι → Submodule R A} [FilteredAlgebra 𝓐] {B : Type w} [Ring B] [Algebra R B]
  {𝓑 : ι → Submodule R B} [FilteredAlgebra 𝓑] {f : A →ₐ[R] B} {i : ι}
  (h : Submodule.map f.toLinearMap (𝓐 i) ≤ 𝓑 i) :
  gradedObject 𝓐 i →ₗ[R] gradedObject 𝓑 i where
  toFun := by
    letI := FilteredModule.gradedObject.mk 𝓑 i
    --letI := LinearMap.restrict f h
    sorry
  map_add' := sorry
  map_smul' := sorry


def toGHom (𝓐 : ι → Submodule R A) [FilteredAlgebra 𝓐] {B : Type w} [Ring B] [Algebra R B]
  (𝓑 : ι → Submodule R B) [FilteredAlgebra 𝓑] (f : A →ₐ[R] B) :
  (⨁ i, assocGAlgebra 𝓐 i) →ₐ[R] (⨁ i, assocGAlgebra 𝓑 i) where
  toFun := sorry
  map_one' := sorry
  map_add' := sorry
  map_mul' := sorry
  map_zero' := sorry
  commutes' := sorry



end FilteredAlgebra

namespace PBW

variable (R : Type u) (L : Type v)
variable [CommRing R] [LieRing L] [LieAlgebra R L]

#check TensorAlgebra.gradedAlgebra

abbrev foo : ℕ → Submodule R (TensorAlgebra R L) :=
  FilteredAlgebra.ofGraded ((LinearMap.range (TensorAlgebra.ι R : L →ₗ[R] TensorAlgebra R L) ^ ·))

abbrev algHom := UniversalEnvelopingAlgebra.mkAlgHom R L

lemma surjF : Function.Surjective (algHom R L) := sorry

abbrev fee : ℕ → Submodule R (UniversalEnvelopingAlgebra R L) :=
  (Submodule.map (algHom R L).toLinearMap).comp (foo R L)


--FilteredAlgebra <| (Submodule.map (algHom R L).toLinearMap).comp (foo R L)

noncomputable instance instFA : FilteredAlgebra (fee R L) :=
  FilteredAlgebra.instPushforwardOfFiltered (foo R L) (algHom R L) (surjF R L)
  -- (FilteredAlgebra.instPushforwardOfFiltered (foo R L) (algHom R L) (surjF R L))

-- abbrev gr := FilteredAlgebra.assocGradedAlgebra (fee R L)

-- noncomputable instance instComm : CommRing (gr R L) where
--   zsmul := sorry
--   add_left_neg := sorry
--   mul_comm := sorry

--abbrev instFilteredUAE : FilteredAlgebra (UniversalEnvelopingAlgebra R L) := sorry

--abbrev assocGradedUAE := FilteredAlgebra.assocGAlgebra

end PBW
