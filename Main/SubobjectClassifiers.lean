import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.CommSq
import Mathlib.CategoryTheory.Types
import Mathlib.CategoryTheory.Limits.Shapes.RegularMono
import Mathlib.CategoryTheory.Subobject.Basic
import Mathlib.CategoryTheory.Category.Cat
--import Mathlib.CategoryTheory.EqToHom
--import Mathlib.CategoryTheory.Subobject.WellPowered

universe u v

open CategoryTheory

variable {C : Type u} [Category.{v, u} C] [Limits.HasTerminal C]

structure StrongSubobjectClassifier (P : MorphismProperty C)
  (h : P ≤ MorphismProperty.monomorphisms C) where
  Ω : C
  map : ⊤_ C ⟶ Ω
  c : ∀ ⦃U X : C⦄ (f : U ⟶ X) [Mono f], X ⟶ Ω
  isPullback : ∀ ⦃U X : C⦄ (f : U ⟶ X) [Mono f],
    CategoryTheory.IsPullback (Limits.terminal.from U) f map (c f)
  isUnique :  ∀ ⦃U X : C⦄ (f : U ⟶ X) [Mono f] (g : X ⟶ Ω),
    CategoryTheory.IsPullback (Limits.terminal.from U) f map g →
    g = (c f)

abbrev SubobjectClassifier (C : Type u) [Category.{v, u} C] [Limits.HasTerminal C] :=
  StrongSubobjectClassifier (MorphismProperty.monomorphisms C) <|
    le_refl (MorphismProperty.monomorphisms C)

class HasStrongSubobjectClassifier (P : MorphismProperty C)
  (h : P ≤ MorphismProperty.monomorphisms C) where
  mk' : Nonempty (StrongSubobjectClassifier P h)

abbrev HasSubobjectClassifier (C : Type u) [Category.{v, u} C] [Limits.HasTerminal C] :=
  HasStrongSubobjectClassifier (MorphismProperty.monomorphisms C) <|
    le_refl (MorphismProperty.monomorphisms C)

noncomputable section

def strongSubobjectClassifier (P : MorphismProperty C)
  (h : P ≤ MorphismProperty.monomorphisms C) [H : HasStrongSubobjectClassifier P h] :=
     Classical.choice <| H.mk'

abbrev subobjectClassifier (C : Type u) [Category.{v, u} C] [Limits.HasTerminal C]
  [HasSubobjectClassifier C] := strongSubobjectClassifier (MorphismProperty.monomorphisms C) <|
    le_refl (MorphismProperty.monomorphisms C)

instance StrongSubobjectClassifier.map_mono {P : MorphismProperty C}
  {h : P ≤ MorphismProperty.monomorphisms C} (S : StrongSubobjectClassifier P h) : Mono S.map :=
    Limits.IsTerminal.mono_from Limits.terminalIsTerminal S.map

namespace SubobjectClassifier

variable {C : Type u} [Category.{v, u} C] [Limits.HasTerminal C] [HasSubobjectClassifier C]

def subobjectPresheaf [Limits.HasPullbacks C] : Functor Cᵒᵖ (Type (max u v)) where
  obj X := Subobject X.unop
  map f := (Subobject.pullback f.unop).obj
  map_id X := by
    ext _
    · simp only [unop_id, types_id_apply]
      erw [Subobject.pullback_id]
    · simp only [unop_id, types_id_apply, eq_mpr_eq_cast, id_eq]

      sorry
  map_comp f g := by
    ext _
    · simp only [unop_comp, types_comp_apply]
      erw [Subobject.pullback_comp]
    ·
      simp only [unop_comp, types_comp_apply, eq_mpr_eq_cast, id_eq]

      sorry


def subobjectPresheaf' (C : Type u) [Category.{v, u} C] [Limits.HasPullbacks C] :
  Functor Cᵒᵖ Cat.{max u v} where
    obj X := Cat.of <| Subobject X.unop
    map f := Subobject.pullback f.unop
    map_id X := by
      apply CategoryTheory.Functor.ext
      · intro _ _ _
        rfl
      · intro _
        erw [Subobject.pullback_id]
        rfl
    map_comp f g := by
      apply CategoryTheory.Functor.ext
      · intro _ _ _
        rfl
      · intro _
        erw [Subobject.pullback_comp]
        rfl


def subobjcetPresheafToType (C : Type u) [Category.{v, u} C] [Limits.HasPullbacks C] :
  Functor Cᵒᵖ (Type max u v) := Functor.comp (subobjectPresheaf' C) <| Cat.objects


-- instance subobjectClassifier_represents_subobjectPresheaf :
--   Functor.Representable.{max u v} (subobjectPresheafToType C) where
--     has_representation := sorry

-- def W {U X : C} (f : U ⟶ X) [Mono f]  := f ≫ Limits.terminal.from X ≫ α.map = f ≫ α.classifying_map f

-- def isLim {U X : C} (f : U ⟶ X) [Mono f] : Limits.IsLimit (Limits.Fork.ofι f (W C α f)) where
--   lift := sorry

-- def equalizerCone {U X : C} (f : U ⟶ X) [Mono f] (c : Limits.Cone
--   (Limits.parallelPair (Limits.terminal.from X ≫ (subobjectClassifier C).map)
--     ((subobjectClassifier C).classifying_map f))) : Cone

instance instRegularMono {U X : C} (f : U ⟶ X) [Mono f] : RegularMono f where
  Z := (subobjectClassifier C).Ω
  left := Limits.terminal.from X ≫ (subobjectClassifier C).map
  right := (subobjectClassifier C).c f
  w := by
    letI := eq_whisker (Limits.terminal.comp_from f) (subobjectClassifier C).map
    simp only [Category.assoc] at this
    rw [this]
    exact ((subobjectClassifier C).isPullback f).w
  isLimit := by
    constructor
    · intro c j

      -- def equalizerCone {U X : C} (f : U ⟶ X) [Mono f] (c : Limits.Cone
--   (Limits.parallelPair (Limits.terminal.from X ≫ (subobjectClassifier C).map)
--     ((subobjectClassifier C).classifying_map f))) : Cone
      letI := (IsPullback.isLimit <| (subobjectClassifier C).isPullback f).lift
      let π := c.π.app
      simp at π


      sorry
    · intro c m j
      sorry
    · intro c
      sorry

-- def subObj_equiv_maps (X : C) [h : Category.{v, u} C] [Limits.HasTerminal C] [HasSubobjectClassifier C] :
--   Subobject X ≃ h.Hom X (subobjectClassifier C).Ω where
--     toFun f := (subobjectClassifier C).classifying_map f.arrow
--     invFun g := by

--       sorry
--     left_inv := sorry
--     right_inv := sorry


instance instRegularMonoCat : RegularMonoCategory C where
  regularMonoOfMono f _ := sorry --instRegularMono C α f


--instance instWellPowered : WellPowered C





-- def fromTer : (⊤_ Type ⟶ Prop) := fun _ => True

-- open Classical

-- noncomputable def fee {U X : Type} (f : U ⟶ X) (x : X) :=
--   propDecidable (∃ (y : U), f y = x)

-- def inducedFun {U X : Type} (f : U ⟶ X) : X ⟶ Prop := fun x =>
--   match fee f x with
--   | isTrue _ => True
--   | isFalse _ => False

-- def propIsPullback {U X : Type} (f : U ⟶ X) [Mono f] :
--   CategoryTheory.IsPullback (Limits.terminal.from U) f fromTer (inducedFun f) where
--     w := by
--       ext x
--       dsimp [inducedFun, fromTer]
--       simp only [true_iff]
--       split
--       trivial
--       sorry
--     isLimit' := sorry

def prop_map : ⊤_ Type ⟶ Prop := fun _ => True

def prop_c {U X : Type} (f : U ⟶ X) [Mono f] : X ⟶ Prop := fun x =>
  match Classical.propDecidable (∃ u, f u = x) with
    | isTrue _ => True
    | isFalse _ => False

@[simp]
lemma terminal_prop_c_eq_true {U X : Type} (f : U ⟶ X) (u : U) :
  (Limits.terminal.from U ≫ prop_map) u = True := by

    sorry


def prop_isPullback {U X : Type} (f : U ⟶ X) [Mono f] :
  CategoryTheory.IsPullback (Limits.terminal.from U) f prop_map (prop_c f) where
    w := by
      ext u
      dsimp [prop_map, prop_c]
      simp only [true_iff]
      cases Classical.propDecidable (∃ v, f v = f u) with
      | isTrue _ => trivial
      | isFalse _ =>
        letI : (∃ v, f v = f u) := exists_apply_eq_apply f u
        contradiction
    isLimit' := by
      constructor
      constructor
      · intro c j
        ext x
        simp only [types_comp_apply, id_eq, eq_mpr_eq_cast, Limits.PullbackCone.mk_pt,
          Limits.PullbackCone.mk_π_app, Functor.const_obj_obj, Limits.cospan_one]

        sorry
      · intro c m j
        simp only [types_comp_apply, id_eq, eq_mpr_eq_cast, Limits.PullbackCone.mk_pt]
        simp only [Limits.PullbackCone.mk_pt] at m
        simp only [types_comp_apply, id_eq, eq_mpr_eq_cast, Limits.PullbackCone.mk_pt,
          Limits.PullbackCone.mk_π_app, Functor.const_obj_obj, Limits.cospan_one] at j

        sorry
      · sorry

instance prop : SubobjectClassifier Type where
  Ω := Prop
  map := fun _ => True
  c U X f _ x :=
    match Classical.propDecidable (∃ u, f u = x) with
    | isTrue _ => True
    | isFalse _ => False
  isPullback U X f _ := by
    constructor
    ·
      sorry
    · sorry
  isUnique := sorry

-- instance set : SubobjectClassifier Prop


end SubobjectClassifier
