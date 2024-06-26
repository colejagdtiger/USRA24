import Mathlib.Algebra.Lie.Basic
import Mathlib.Algebra.Lie.Free
import Mathlib.Algebra.Lie.UniversalEnveloping
import Mathlib.Algebra.FreeMonoid.Count

universe u v w



-- inductive Reps where
--   | one : Reps
--   | of (x : X) : Reps
--   | mul : Reps → Reps → Reps

-- instance : One (Reps X) where
--   one := .one

-- instance : Mul (Reps X) where
--   mul := .mul


-- inductive Rel : Reps X → Reps X → Prop
--   | mul_compat (x x' y y' : Reps X) : Rel x x' → Rel y y' → Rel (x * y) (x' * y')
--   | mul_assoc (x y z : Reps X) : Rel ((x * y) *z) (x * (y * z))
--   | one_mul (x : Reps X) : Rel (1 * x) x
--   | mul_one (x : Reps X) : Rel (x * 1) x
--   | mul_comm (x y : Reps X) : Rel (x * y) (y * x)
--   | refl (x : Reps X) : Rel x x
--   | symm (x y : Reps X) : Rel x y → Rel y x
--   | trans (x y z : Reps X) : Rel x y → Rel y z → Rel x z

-- def FreeCommMonoid.setoid : Setoid (Reps X) where
--   r := Rel X
--   iseqv := ⟨Rel.refl, Rel.symm _ _, Rel.trans _ _ _⟩

-- def FreeCommMonoid := Quotient (FreeCommMonoid.setoid X)

-- def FreeCommMonoid.mk : Reps X → FreeCommMonoid X := Quotient.mk _

-- instance : Mul (FreeCommMonoid X) where
--   mul := Quotient.lift₂ (fun x y => Quotient.mk _ (x * y)) <|
--     fun _ _ _ _ h₁ h₂ => Quotient.sound <| Rel.mul_compat _ _ _ _ h₁ h₂

-- instance : One (FreeCommMonoid X) where
--   one := Quotient.mk _ 1

-- lemma FreeCommMonoid.mk_surjective : Function.Surjective (FreeCommMonoid.mk X) := by
--   rintro ⟨x⟩
--   exact ⟨x, rfl⟩


-- instance : CommMonoid (FreeCommMonoid X) where
--   mul_assoc x y z := by
--     obtain ⟨x,rfl⟩ := FreeCommMonoid.mk_surjective _ x
--     obtain ⟨y,rfl⟩ := FreeCommMonoid.mk_surjective _ y
--     obtain ⟨z,rfl⟩ := FreeCommMonoid.mk_surjective _ z
--     exact Quotient.sound <| Rel.mul_assoc x y z
--   one_mul x := by
--     obtain ⟨x,rfl⟩ := FreeCommMonoid.mk_surjective _ x
--     exact Quotient.sound <| Rel.one_mul _
--   mul_one x := by
--     obtain ⟨x,rfl⟩ := FreeCommMonoid.mk_surjective _ x
--     exact Quotient.sound <| Rel.mul_one _
--   mul_comm x y := by
--     obtain ⟨x,rfl⟩ := FreeCommMonoid.mk_surjective _ x
--     obtain ⟨y,rfl⟩ := FreeCommMonoid.mk_surjective _ y
--     exact Quotient.sound <| Rel.mul_comm x y


-- #check FreeMonoid

-- variable (M : Type v) [Monoid M]

-- inductive Rel : M → M → Prop
--   | mul_compat (x x' y y' : M) : Rel x x' → Rel y y' → Rel (x * y) (x' * y')
--   | mul_comm (x y : M) : Rel (x * y) (y * x)
--   | refl (x : M) : Rel x x
--   | symm (x y : M) : Rel x y → Rel y x
--   | trans (x y z : M) : Rel x y → Rel y z → Rel x z

-- def Co.setoid : Setoid (FreeMonoid X) where
--   r := Rel M
--   iseqv := ⟨Rel.refl, Rel.symm _ _, Rel.trans _ _ _⟩

-- def FreeCommMonoid := Quotient (FreeCommMonoid.setoid X)

-- def FreeCommMonoid.mk : FreeMonoid X → FreeCommMonoid X := Quotient.mk _

-- def FreeCommMonoid.of {X : Type v} (x : X) : FreeCommMonoid X := FreeCommMonoid.mk X <| FreeMonoid.of x

-- instance : Mul (FreeCommMonoid X) where
--   mul := Quotient.lift₂ (fun x y => Quotient.mk _ (x * y)) <|
--     fun _ _ _ _ h₁ h₂ => Quotient.sound <| Rel.mul_compat _ _ _ _ h₁ h₂

-- instance : One (FreeCommMonoid X) where
--   one := Quotient.mk _ 1

-- lemma FreeCommMonoid.mk_surjective : Function.Surjective (FreeCommMonoid.mk X) := by
--   rintro ⟨x⟩
--   exact ⟨x, rfl⟩

-- instance : CommMonoid (FreeCommMonoid X) where
--   mul_assoc x y z := by
--     obtain ⟨x,rfl⟩ := FreeCommMonoid.mk_surjective _ x
--     obtain ⟨y,rfl⟩ := FreeCommMonoid.mk_surjective _ y
--     obtain ⟨z,rfl⟩ := FreeCommMonoid.mk_surjective _ z
--     apply Quotient.sound --<| Rel.refl (x * (y * z))
--     rw [mul_assoc]
--     exact Rel.refl (x * (y * z))
--   one_mul x := by
--     obtain ⟨x,rfl⟩ := FreeCommMonoid.mk_surjective _ x
--     apply Quotient.sound
--     rw [one_mul]
--     exact Rel.refl x
--   mul_one x := by
--     obtain ⟨x,rfl⟩ := FreeCommMonoid.mk_surjective _ x
--     apply Quotient.sound
--     rw [mul_one]
--     exact Rel.refl x
--   mul_comm x y := by
--     obtain ⟨x,rfl⟩ := FreeCommMonoid.mk_surjective _ x
--     obtain ⟨y,rfl⟩ := FreeCommMonoid.mk_surjective _ y
--     exact Quotient.sound <| Rel.mul_comm x y


-- def Comm.homLift {H : Type} [Group H] (f : M →* H) : Groupification M →* H where
--   toFun := Groupification.lift M f
--   map_one' := Reps.homLift_one M f
--   map_mul' := by rintro ⟨x⟩ ⟨y⟩ ; rfl


-- def FreeCommMonoid.count {X : Type v} (x : X) [DecidableEq X] : FreeCommMonoid X →* Multiplicative ℕ :=
--   sorry





namespace Comm

variable (M : Type u) [Mul M]

inductive Rel : M → M → Prop
  | mul_compat (x x' y y' : M) : Rel x x' → Rel y y' → Rel (x * y) (x' * y')
  | mul_comm (x y : M) : Rel (x * y) (y * x)
  | refl (x : M) : Rel x x
  | symm (x y : M) : Rel x y → Rel y x
  | trans (x y z : M) : Rel x y → Rel y z → Rel x z

def Abelianization.setoid : Setoid M where
  r := Rel M
  iseqv := ⟨Rel.refl, Rel.symm _ _, Rel.trans _ _ _⟩

def Abelianization := Quotient (Abelianization.setoid M)

def Abelianization.mk : M →  Abelianization M := Quotient.mk _

instance : Mul (Abelianization M) where
  mul := Quotient.lift₂ (fun x y => Quotient.mk _ (x * y)) <|
    fun _ _ _ _ h₁ h₂ => Quotient.sound <| Rel.mul_compat _ _ _ _ h₁ h₂

lemma  Abelianization.mk_surjective : Function.Surjective (Abelianization.mk M) := by
  rintro ⟨x⟩
  exact ⟨x, rfl⟩

instance (M : Type u) [Monoid M] : CommMonoid (Abelianization M) where
  mul_comm x y := by
    obtain ⟨x,rfl⟩ := Abelianization.mk_surjective _ x
    obtain ⟨y,rfl⟩ :=  Abelianization.mk_surjective _ y
    exact Quotient.sound <| Rel.mul_comm x y
  mul_assoc x y z := by
    obtain ⟨x,rfl⟩ := Abelianization.mk_surjective _ x
    obtain ⟨y,rfl⟩ := Abelianization.mk_surjective _ y
    obtain ⟨z,rfl⟩ := Abelianization.mk_surjective _ z
    apply Quotient.sound
    rw [mul_assoc]
    exact Rel.refl (x * (y * z))
  one := Abelianization.mk M 1
  mul_one x := by
    obtain ⟨x,rfl⟩ := Abelianization.mk_surjective _ x
    apply Quotient.sound
    rw [mul_one]
    exact Rel.refl x
  one_mul x := by
    obtain ⟨x,rfl⟩ := Abelianization.mk_surjective _ x
    apply Quotient.sound
    rw [one_mul]
    exact Rel.refl x


end Comm



variable (X : Type v) [DecidableEq X]

def FreeCommMonoid := Comm.Abelianization <| FreeMonoid X

namespace FreeCommMonoid

end FreeCommMonoid



namespace PBW

variable (R : Type u) (X : Type v) [CommRing R] [LE X] (ι : Type w)

def incl : FreeCommMonoid X → UniversalEnvelopingAlgebra R (FreeLieAlgebra R X) := fun x => sorry


def Basis : Basis (FreeCommMonoid X) R <| UniversalEnvelopingAlgebra R (FreeLieAlgebra R X) := by
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
