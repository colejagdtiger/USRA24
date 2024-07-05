import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.Algebra.Homology.ComplexShape
import Mathlib.Order.WithBot
import Mathlib.Order.SuccPred.Basic
import Mathlib.CategoryTheory.Subobject.Basic
import Mathlib.CategoryTheory.Subobject.Lattice

universe u v w

open CategoryTheory

variable {C : Type u} {α : Type w}
[CategoryTheory.Category.{v, u} C] [Preorder α]

def MonoOver.Cocone {X : C} (F : α ⥤ MonoOver X) : Limits.Cocone F where
  pt := ⊤
  ι := { app := fun _ => MonoOver.leTop (F.obj _) }


class Filtration {X : C} (F : α ⥤ MonoOver X) where
  is_colimit : Limits.IsColimit (MonoOver.Cocone F)



namespace Filtration

noncomputable def indexedGradedObject [Limits.HasZeroMorphisms C] {X : C} (F : α ⥤ MonoOver X)
  [Filtration F] (a : α) [Limits.HasCokernel <| MonoOver.arrow (F.obj a) ] : C :=
    Limits.cokernel <| MonoOver.arrow (F.obj a)

--noncomputable def gradedObject

end Filtration
