import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.Algebra.Homology.ComplexShape
import Mathlib.Order.WithBot
import Mathlib.Order.SuccPred.Basic
import Mathlib.CategoryTheory.Subobject.Basic
import Mathlib.CategoryTheory.Subobject.Lattice
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Transport

universe u v w

open CategoryTheory

variable {C : Type u} {α : Type w}
[CategoryTheory.Category.{v, u} C] [Preorder α] [PredOrder α]


--namespaces
def exhaustiveCocone {X : C} (F : α ⥤ MonoOver X) : Limits.Cocone F where
  pt := ⊤
  ι := { app := fun _ => MonoOver.leTop (F.obj _) }

def hausdorffCone {X : C} (F : α ⥤ MonoOver X) [Limits.HasInitial C] : Limits.Cone F :=
  sorry
  --pt := ⊥
  --π := { app}

#check Over.forget



-- more general? Fix issues here
--{m : MonoidalCategory.tensorObj X X ⟶ X} {u : MonoidalCategory.tensorUnit ⟶ X}


class Over.TensorData (X : C) [MonoidalCategory.{v, u} C] where
  m : MonoidalCategory.tensorObj X X ⟶ X
  u : MonoidalCategory.tensorUnit ⟶ X

def Over.TensorData.mul (X : C) [MonoidalCategory.{v, u} C] [Over.TensorData X] :
  MonoidalCategory.tensorObj X X ⟶ X := m

def Over.TensorData.unit (X : C) [MonoidalCategory.{v, u} C] [Over.TensorData X] :
  MonoidalCategory.tensorUnit ⟶ X := u

variable {X : C} [MonoidalCategory.{v, u} C] [Over.TensorData X]


def Over.tensorObjBase : Over X → Over X → Over (MonoidalCategory.tensorObj X X) :=
  fun f g => Over.mk <| MonoidalCategory.tensorHom f.hom g.hom

def Over.tensorObj : Over X → Over X → Over X := fun f g =>
  (Over.map (TensorData.mul X)).obj <| tensorObjBase f g

def Over.tensorUnit : Over X := Over.mk <| Over.TensorData.unit X

-- These have bad names
@[simp]
lemma Over.tensorObjBase_obj_eq {f g : Over X} :
  (tensorObjBase f g).left = MonoidalCategory.tensorObj f.left g.left := rfl

@[simp]
lemma Over.tensorObj_hom_eq {f g : Over X} :
  (tensorObjBase f g).hom = MonoidalCategory.tensorHom f.hom g.hom := rfl

@[simp]
lemma Over.baseTensorObjBase_obj_eq {f g : Over X} :
  MonoidalCategory.tensorObj f.left g.left = (tensorObj f g).left := rfl

-- lemma Over.tensorObj_hom_eq {f g : Over X} :
--   MonoidalCategory.tensorHom f.hom g.hom = (tensorObj f g).hom := rfl

@[simp]
lemma Over.baseTensorHom_eq {f g : Over X} :
  (tensorObj f g).hom = MonoidalCategory.tensorHom f.hom g.hom ≫ (TensorData.mul X) := rfl


lemma Over.helper {f g₁ g₂ : Over X} {h : g₁ ⟶ g₂} :
  MonoidalCategory.whiskerLeft f.left (h.left) ≫
  (tensorObjBase f g₂).hom = (tensorObjBase f g₁).hom := by
    simp
    let H : h.left ≫ g₂.hom = g₁.hom := by
      simp only [Functor.const_obj_obj, Over.w]

    sorry


def Over.whiskerLeft_base (f : Over X) {g₁ g₂ : Over X} (h : g₁ ⟶ g₂) :
  tensorObjBase f g₁ ⟶ tensorObjBase f g₂ := by
    --dsimp [tensorObj]
    letI := (Over.forget X).map h

    letI := MonoidalCategory.whiskerLeft f.left this
    simp at this
    --letI := Over.homMk this
    -- exact Over.homMk this
    --letI := Over.homMk this
    -- have h₁ : MonoidalCategory.tensorObj f.left g₁.left = (Over.tensorObj m f g₁).left := by
    --   dsimp [tensorObj]
    -- have h₂ : MonoidalCategory.tensorObj f.left g₂.left = (Over.tensorObj m f g₂).left := by
    --   dsimp [tensorObj]
    -- rw [h₁, h₂] at this

    sorry


-- instance instMonStruct :
--   MonoidalCategoryStruct (Over X) where
--     tensorObj f g := Over.mk <| MonoidalCategory.tensorHom f.hom g.hom ≫ m
--     tensorUnit := Over.mk u
--     whiskerLeft f g₁ g₂ h := by
--       letI := (Over.forget X).map h
--       letI := MonoidalCategory.whiskerLeft f.left this
--       simp at this
--       simp

--       sorry
--     whiskerRight := sorry
--     associator := sorry
--     leftUnitor := sorry
--     rightUnitor := sorry

-- def Over.inducingData : Monoidal.InducingFunctorData (Over.forget X) := sorry

-- structure ascFiltration {X : C} where
--   F : α ⥤ MonoOver X
--   exhaustive : Limits.IsColimit (exhaustiveCocone F)

-- def ascFiltration.isHausdorff (F : ascFiltration) : Prop := sorry

structure FObject (X : C) where
  fil : sorry
-- class NonUnitalAlgebraFiltration {X : C} (F : α ⥤ MonoOver X) [MonoidalCategory C] extends Filtration F where
--   hom : MonoidalCategory.tensorObj X X ⟶ X


-- class AlgebraFiltration {X : C} (F : α ⥤ MonoOver X) [MonoidalCategory C] extends NonUnitalAlgebraFiltration F where
--   unit : MonoidalCategory.tensorUnit ⟶ X


-- namespace Filtration

-- -- Currently this is an object of MonoOver X
-- noncomputable def indexedGradedObject {X : C} [Limits.HasZeroMorphisms <| MonoOver X] (F : α ⥤ MonoOver X)
--   [Filtration F] (a : α) [Limits.HasCokernel <| F.map (homOfLE (Order.pred_le a)) ] :=
--     Limits.cokernel <| F.map (homOfLE (Order.pred_le a))

-- --noncomputable def gradedObject

-- end Filtration
