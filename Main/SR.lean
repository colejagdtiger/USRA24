variable {A : Type} {R : A → A → Prop} (x : A) (h : acc R x)

--def my_rec : ∀ x : A, acc R x → ℕ := @acc.rec A R (λ _ ℕ)
