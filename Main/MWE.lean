import Mathlib.CategoryTheory.Subobject.Basic
import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

universe u v

open CategoryTheory

variable {C : Type u} [Category.{v, u} C] [Limits.HasTerminal C]

noncomputable section

@[simp]
lemma equ : Type max (v+1) v (u+1) = Type ((max u v) + 1) := rfl

def subobjectPresheaf [Limits.HasPullbacks C] : Functor Cᵒᵖ Cat.{max u v, max u v} where
  obj X := Cat.of <| Subobject X.unop
  map f := Subobject.pullback f.unop
  map_id X := by
    simp only [unop_id]
    --apply Subobject.pullback_id

    sorry
  map_comp := sorry

-- def subobjectPresheaf' [Limits.HasPullbacks C] : Functor Cᵒᵖ (Type (max u v)) where
--   obj X := Subobject X.unop
--   map f := (Subobject.pullback f.unop).obj
