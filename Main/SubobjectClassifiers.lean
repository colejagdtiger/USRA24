import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.CommSq
import Mathlib.CategoryTheory.Types
import Mathlib.CategoryTheory.Limits.Shapes.RegularMono
import Mathlib.CategoryTheory.Subobject.Basic
import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Subobject.Lattice
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

section lemmas

variable {C : Type u} [Category.{v, u} C] [Limits.HasTerminal C] {U X : C} (f : U ⟶ X) [Mono f]
  (s : SubobjectClassifier C)

@[simp]
lemma comp_factor_eq_map :
  f ≫ Limits.terminal.from X ≫ s.map = f ≫ s.c f := by
    letI := eq_whisker (Limits.terminal.comp_from f) s.map
    simp only [Category.assoc] at this
    rw [this]
    exact (s.isPullback f).w

lemma terminal_map_eq_forkι_classifiying
  (c : Limits.Cone (Limits.parallelPair (Limits.terminal.from X ≫ s.map) (s.c f))) :
  (Limits.terminal.from c.pt) ≫ s.map = (Limits.Fork.ι c) ≫ (s.c f) := by


    sorry

def forkConeToPullbackCone.app
  (c : Limits.Cone (Limits.parallelPair (Limits.terminal.from X ≫ s.map) (s.c f))) :
  (Functor.const Limits.WalkingCospan).obj c.pt ⟶ Limits.cospan (s.c f) s.map := by

    sorry

def forkConeToPullbackCone
  (c : Limits.Cone (Limits.parallelPair (Limits.terminal.from X ≫ s.map) (s.c f))) :
  CategoryTheory.Limits.PullbackCone (s.c f) s.map where
    pt := c.pt
    π := by

      sorry


def fork := Limits.Fork.ofι f (comp_factor_eq_map f s)

def lift (c : Limits.Cone (Limits.parallelPair (Limits.terminal.from X ≫ s.map) (s.c f))) :
  c.pt ⟶ (fork f s).pt :=
    (IsPullback.isLimit <| s.isPullback f).lift <|
    Limits.PullbackCone.mk (Limits.terminal.from c.pt) (Limits.Fork.ι c) <|
    terminal_map_eq_forkι_classifiying f s c

def aux (c : Limits.Cone (Limits.parallelPair (Limits.terminal.from X ≫ s.map) (s.c f))) :=
  (IsPullback.isLimit <| s.isPullback f).fac <|
    Limits.PullbackCone.mk (Limits.terminal.from c.pt) (Limits.Fork.ι c) <|
    terminal_map_eq_forkι_classifiying f s c

-- lemma fas_zero (c : Limits.Cone (Limits.parallelPair (Limits.terminal.from X ≫ s.map) (s.c f))) :
--   (fork f s).π.app Limits.WalkingParallelPair.zero =  (aux f s c) Limits.WalkingCospan.left := by

--     sorry

def fac (c : Limits.Cone (Limits.parallelPair (Limits.terminal.from X ≫ s.map) (s.c f)))
  (j : Limits.WalkingParallelPair) : (lift f s c) ≫ (fork f s).π.app j = c.π.app j := by
    letI := (IsPullback.isLimit <| s.isPullback f).fac <|
      Limits.PullbackCone.mk (Limits.terminal.from c.pt) (Limits.Fork.ι c) <|
      terminal_map_eq_forkι_classifiying f s c

    cases j with
    | zero =>
      let h := this Limits.WalkingCospan.left
      simp at h

      sorry
    | one => sorry


def fine :
  Limits.IsLimit (fork f s) where
    lift c := lift f s c
    fac c j := by
      letI := (IsPullback.isLimit <| s.isPullback f).fac <|
        Limits.PullbackCone.mk (Limits.terminal.from c.pt) (Limits.Fork.ι c) <|
        terminal_map_eq_forkι_classifiying f s c

      sorry
    uniq := sorry


end lemmas

variable {C : Type u} [Category.{v, u} C] [Limits.HasTerminal C] [HasSubobjectClassifier C]

-- @[simp]
-- lemma foo {X : C} (x : Subobject X) [Limits.HasPullbacks C] :
--   (Subobject.underlying.obj ((Subobject.pullback (𝟙 X)).obj x) ⟶ X) =
--     (Subobject.underlying.obj x ⟶ X) := by
--       simp only [Subobject.pullback_id]

-- lemma fee {X : C} (x : Subobject X) [Limits.HasPullbacks C] :
--   ((Subobject.pullback (𝟙 X)).obj x).arrow = x.arrow := by
--   sorry

def subobjectPresheaf [Limits.HasPullbacks C] : Functor Cᵒᵖ (Type (max u v)) where
  obj X := (Subobject X.unop)
  map f := (Subobject.pullback f.unop).obj
  map_id X := by
    ext U
    · simp only [types_id_apply]
      erw [Subobject.pullback_id]
    · simp at U
      simp only [unop_id, types_id_apply, eq_mpr_eq_cast, id_eq]


      sorry
    -- ext _
    -- · simp only [unop_id, types_id_apply]
    --   erw [Subobject.pullback_id]
    -- · simp only [unop_id, types_id_apply, eq_mpr_eq_cast, id_eq]
    --   dsimp [Subobject.arrow]
    --   --dsimp [Subobject.representative.obj]
    --   erw [Subobject.pullback_id]
  map_comp f g := by
    ext _
    · simp only [unop_comp, types_comp_apply]
      erw [Subobject.pullback_comp]
    ·
      simp only [unop_comp, types_comp_apply, eq_mpr_eq_cast, id_eq]

      sorry


-- def subobjectPresheaf' (C : Type u) [Category.{v, u} C] [Limits.HasPullbacks C] :
--   Functor Cᵒᵖ Cat.{max u v} where
--     obj X := Cat.of <| Subobject X.unop
--     map f := Subobject.pullback f.unop
--     map_id X := by
--       apply CategoryTheory.Functor.ext
--       · intro _ _ _
--         rfl
--       · intro _
--         erw [Subobject.pullback_id]
--         rfl
--     map_comp f g := by
--       apply CategoryTheory.Functor.ext
--       · intro _ _ _
--         rfl
--       · intro _
--         erw [Subobject.pullback_comp]
--         rfl

def test := ULift.{max u v, u} C


instance subobjectClassifier_represents (C : Type u) [Category.{max u v, u} C] [Limits.HasPullbacks C]
  : Functor.Representable (CategoryTheory.Subobject.functor C) where
    has_representation := sorry

-- instance subobjectClassifier_represents_subobjectPresheaf [Limits.HasPullbacks C] :
--   Functor.Representable (subobjectPresheafToType C) where
--     has_representation := sorry

-- def W {U X : C} (f : U ⟶ X) [Mono f]  := f ≫ Limits.terminal.from X ≫ α.map = f ≫ α.classifying_map f

-- def isLim {U X : C} (f : U ⟶ X) [Mono f] : Limits.IsLimit (Limits.Fork.ofι f (W C α f)) where
--   lift := sorry

-- def equalizerCone {U X : C} (f : U ⟶ X) [Mono f] (c : Limits.Cone
--   (Limits.parallelPair (Limits.terminal.from X ≫ (subobjectClassifier C).map)
--     ((subobjectClassifier C).classifying_map f))) : Cone

-- def aoo {X Y : C} {f g : X ⟶ Y} (t : CategoryTheory.Limits.Fork f g) : sorry := sorry

instance instRegularMono {U X : C} (f : U ⟶ X) [Mono f] : RegularMono f where
  Z := (subobjectClassifier C).Ω
  left := Limits.terminal.from X ≫ (subobjectClassifier C).map
  right := (subobjectClassifier C).c f
  isLimit := fine f <| subobjectClassifier C
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
