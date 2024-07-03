import Mathlib.Algebra.Lie.Basic
import Mathlib.Algebra.Lie.Free
import Mathlib.Algebra.RingQuot
import Mathlib.LinearAlgebra.TensorAlgebra.Basic

universe u v w

open scoped DirectSum


namespace SymmAlgebra

variable (R : Type u) (M : Type v) [CommSemiring R] [AddCommMonoid M] [Module R M]

inductive Rel : TensorAlgebra R M → TensorAlgebra R M → Prop
  | comm : Rel (x * y) (y * x)

end SymmAlgebra

def SymmAlgebra (R : Type u) (M : Type v) [CommSemiring R] [AddCommMonoid M] [Module R M] :=
  RingQuot (SymmAlgebra.Rel R M)

namespace SymmAlgebra

variable (R : Type u) (M : Type v) [CommSemiring R] [AddCommMonoid M] [Module R M]

instance instInhabited : Inhabited (SymmAlgebra R M) := RingQuot.instInhabited _

instance instSemiring : Semiring (SymmAlgebra R M) := RingQuot.instSemiring _

instance instAlgebra : Algebra R (SymmAlgebra R M) :=
  inferInstanceAs (Algebra R (RingQuot (Rel R M)))

def mkAlgHom : TensorAlgebra R M →ₐ[R] SymmAlgebra R M :=
  RingQuot.mkAlgHom R (Rel R M)

def ι : M →ₗ[R] SymmAlgebra R M := LinearMap.comp (mkAlgHom R M) (TensorAlgebra.ι R)

end SymmAlgebra


namespace UniversalEnvelopingAlgebra

variable (R : Type u) (L : Type v)
variable [CommRing R] [LieRing L] [LieAlgebra R L]

def Tn (n : ℕ) := match n with
  | 0 => LinearMap.range (TensorAlgebra.ι R : L →ₗ[_] _) ^ 0
  | n + 1 => Submodule.span R <|
    Set.union (Tn n).carrier (LinearMap.range (TensorAlgebra.ι R : L →ₗ[_] _) ^ (n + 1)).carrier

def fee (n : ℕ) := (LinearMap.range <|
  (mkAlgHom R L).toLinearMap.comp (TensorAlgebra.ι R : L →ₗ[_] _)) ^ n

def Un (n : ℕ) : Submodule R (UniversalEnvelopingAlgebra R L) :=
  Submodule.span R <| ⋃ (i : {i : ℕ | i ≤ n}), ((LinearMap.range <|
    (mkAlgHom R L).toLinearMap.comp (TensorAlgebra.ι R : L →ₗ[_] _)) ^ (i : ℕ)).carrier

def Un' (n : ℕ) : Submodule R (UniversalEnvelopingAlgebra R L) :=
  iSup fun i : {k : ℕ | k ≤ n} => (LinearMap.range <|
    (mkAlgHom R L).toLinearMap.comp (TensorAlgebra.ι R : L →ₗ[_] _)) ^ (i : ℕ)

def Un_map (n m : ℕ) (h : n ≤ m) : Un R L n →ₗ[R] Un R L m where
  toFun := by
    intro x
    induction m with
    | zero =>
      simp only [Nat.zero_eq, nonpos_iff_eq_zero] at h
      rw [h] at x
      exact x

    | succ m ih =>
      dsimp [Un]
      have h' : n ≤ m ∨ n = m + 1 := sorry
      sorry
  map_add' := sorry
  map_smul' := sorry

def LEMem (n m : ℕ) (h : n ≤ m) : Un R L n ≤ Un R L m := by
  apply Submodule.span_mono
  simp [Set.mem_iUnion]
  intro i h₁ x h₂
  simp [Set.mem_iUnion]
  use i
  exact ⟨h₁.trans h, h₂⟩


def UnMul (n M : ℕ) : Un R L n → Un R L m → Un R L (n + m) := sorry

def LEMem' (n m : ℕ) (h : n ≤ m) : Un' R L n ≤ Un' R L m := by
  dsimp [Un']
  sorry

--def fee (n : ℕ) : Submodule R L where
--(Un R L (n + 1)) (Un R L n) }

-- def Gn (n : ℕ) : Submodule R ((UniversalEnvelopingAlgebra R L) ⧸ (Un R L n)) := match n with
--   | 0 => sorry--(Un R L 0)
--   | n + 1 => by
--     let h := Un R L (n + 1) ⧸ (LinearMap.range <| Un_map R L n (n + 1)
--     (by simp only [le_add_iff_nonneg_right, zero_le]))
--     --exact h
--     sorry

-- Want to remove this
def foo (n : ℕ) := match n with
  | 0 => ⊥
  | n + 1 => Un R L n

def Gn (n : ℕ) : Submodule R ((UniversalEnvelopingAlgebra R L) ⧸ foo R L n) := match n with
  | 0 => Submodule.map (⊥ : Submodule R (UniversalEnvelopingAlgebra R L)).mkQ (Un R L 0)
  | n + 1 => Submodule.map (Un R L n).mkQ (Un R L (n + 1))



def assocGraded := ⨁ n : ℕ, Gn R L n

namespace assocGraded

instance instInhabited : Inhabited (assocGraded R L) := sorry

instance instSemiring : Semiring (assocGraded R L) := sorry

instance instAlgebra : Algebra R (assocGraded R L) := sorry

def ι : UniversalEnvelopingAlgebra R L →ₗ[R] assocGraded R L := sorry

end assocGraded

end UniversalEnvelopingAlgebra

namespace PBW

variable (R : Type u) (X : Type v) [CommRing R]

--corrdinate free!
#check SymmAlgebra R (FreeLieAlgebra R X)




#check UniversalEnvelopingAlgebra R (FreeLieAlgebra R X)


--coordinate approach
variable (R : Type u) (X : Type v) [CommRing R] [LE X]

def incl : (X →₀ ℕ) → UniversalEnvelopingAlgebra R (FreeLieAlgebra R X) := sorry

def Basis : Basis (X →₀ ℕ) R <| UniversalEnvelopingAlgebra R (FreeLieAlgebra R X) := by
  sorry

theorem Free : Module.Free R <| UniversalEnvelopingAlgebra R (FreeLieAlgebra R X) :=
    Module.Free.of_basis <| PBW.Basis R X

end PBW

def commuatation_factor (R : Type u) (A : Type v) [CommRing R] [CommGroup A] : sorry := sorry

-- class ColorLieRing (A : Type v) (L : Type w) [CommGroup A] [AddCommGroup L] [Bracket L L] where
--   /-- A Color Lie ring bracket is additive in its first component. -/
--   protected add_lie : ∀ x y z : L, ⁅x + y, z⁆ = ⁅x, z⁆ + ⁅y, z⁆
--   /-- A Color Lie ring bracket is additive in its second component. -/
--   protected lie_add : ∀ x y z : L, ⁅x, y + z⁆ = ⁅x, y⁆ + ⁅x, z⁆
--   /-- A Color Lie ring bracket vanishes on the diagonal in L × L. -/
--   protected lie_self : ∀ x : L, ⁅x, x⁆ = 0
--   /-- A Color Lie ring bracket satisfies a Leibniz / Jacobi identity. -/
--   protected leibniz_lie : ∀ x y z : L, ⁅x, ⁅y, z⁆⁆ = ⁅⁅x, y⁆, z⁆ + ⁅y, ⁅x, z⁆⁆

class ColorLieAlgebra (R : Type u) (A : Type v) (L : Type w) [CommGroup A] [CommRing R] [AddCommGroup L] [Bracket L L] [Module R L]
 --extends AddCommGroup L, Bracket L L, Module R L
 where
  /-- A Color Lie ring bracket is additive in its first component. -/
  protected add_lie : ∀ x y z : L, ⁅x + y, z⁆ = ⁅x, z⁆ + ⁅y, z⁆
  /-- A Color Lie ring bracket is additive in its second component. -/
  protected lie_add : ∀ x y z : L, ⁅x, y + z⁆ = ⁅x, y⁆ + ⁅x, z⁆
  /-- A Color Lie ring bracket vanishes on the diagonal in L × L. -/
  protected lie_self : ∀ x : L, ⁅x, x⁆ = 0
  /-- A Color Lie ring bracket satisfies a Leibniz / Jacobi identity. -/
  protected leibniz_lie : ∀ x y z : L, ⁅x, ⁅y, z⁆⁆ = ⁅⁅x, y⁆, z⁆ + ⁅y, ⁅x, z⁆⁆
