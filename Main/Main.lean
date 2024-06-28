import Mathlib.Algebra.Lie.Basic
import Mathlib.Algebra.Lie.Free
import Mathlib.Algebra.RingQuot
import Mathlib.LinearAlgebra.TensorAlgebra.Basic

universe u v w

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

def ι : M →ₗ[R] SymmAlgebra R M := sorry


end SymmAlgebra


namespace UniversalEnvelopingAlgebra

variable (R : Type u) (L : Type v)
variable [CommRing R] [LieRing L] [LieAlgebra R L]

def Un (n : ℕ) := TensorAlgebra R L

def assocGraded : ℕ → TensorAlgebra R L := sorry



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
