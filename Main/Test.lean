import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Lie.Basic
import Mathlib.Tactic


universe u v

variable (R : Type u) (A : Type v) [CommRing R] [Ring A] [Algebra R A]

instance : Bracket A A where
  bracket a b :=  a * b - b * a


instance : LieRing A where
  add_lie a b c := by
    dsimp [Bracket.bracket]
    rw [right_distrib, left_distrib]
    abel
  lie_add a b c := by
    dsimp [Bracket.bracket]
    rw [right_distrib, left_distrib]
    abel
  lie_self a := by
    exact sub_self <| a * a
  leibniz_lie a b c := by
    dsimp [Bracket.bracket]
    rw [mul_sub_left_distrib, mul_sub_right_distrib]
    rw [mul_sub_left_distrib, mul_sub_right_distrib]
    rw [mul_sub_left_distrib, mul_sub_right_distrib]
    group
    abel
