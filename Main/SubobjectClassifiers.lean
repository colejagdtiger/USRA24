import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Cospan

universe u v

open CategoryTheory

variable {C : Type u} [Category.{v, u} C] [Limits.HasTerminal C]

-- structure SubobjectClassifier.Square where
--   Square :

def SubobjectClassifier.Square {Ω : C} (f : U ⟶ X) (s : X ⟶ Ω) (t : ⊤_ C ⟶ Ω) :
  Limits.Cone (Limits.cospan t s) where


class SubobjectClassifier (Ω : C) where
  from_terminal : ⊤_ C ⟶ Ω
  mono' : Mono from_terminal
  --cartesian : {U X : C} → (f : U ⟶ X) → Mono f → ∃! (g : X ⟶ Ω), Mono g ∧
