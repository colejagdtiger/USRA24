import Mathlib.Algebra.Lie.Basic

universe u v w

--theorem PBW (R : Type u) (X : Type w) (L : FreeLieAlgebra R X) : sorry := sorry
#eval 18 + 19

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
