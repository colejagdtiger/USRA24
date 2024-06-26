import Mathlib.Algebra.FreeMonoid.Basic
import Mathlib.Algebra.Free

universe u

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

instance : CommMagma (Abelianization M) where
  mul_comm x y := by
    obtain ⟨x,rfl⟩ := Abelianization.mk_surjective _ x
    obtain ⟨y,rfl⟩ :=  Abelianization.mk_surjective _ y
    exact Quotient.sound <| Rel.mul_comm x y

instance (M : Type u) [MulOneClass M] : MulOneClass (Abelianization M) where
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


instance (M : Type u) [Semigroup M] : CommSemigroup (Abelianization M) where
  mul_comm := mul_comm
  mul_assoc x y z := by
    obtain ⟨x,rfl⟩ := Abelianization.mk_surjective _ x
    obtain ⟨y,rfl⟩ := Abelianization.mk_surjective _ y
    obtain ⟨z,rfl⟩ := Abelianization.mk_surjective _ z
    apply Quotient.sound
    rw [mul_assoc]
    exact Rel.refl (x * (y * z))

instance (M : Type u) [Monoid M] : CommMonoid (Abelianization M) where
  mul_comm := mul_comm
  mul_one := mul_one
  one_mul := one_mul

end Comm

variable (α : Type u)

def FreeCommMagma := Comm.Abelianization <| FreeMagma α

namespace FreeCommMagma

end FreeCommMagma

def FreeCommSemigroup := Comm.Abelianization <| FreeSemigroup α

namespace FreeCommSemiGroup

end FreeCommSemiGroup

def FreeCommMonoid := Comm.Abelianization <| FreeMonoid α

namespace FreeCommMonoid

end FreeCommMonoid
