module Thesis.Relation.Meet where

open import Thesis.Relation

open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)

_∩_ : {I : Set} {X Y : I → Set} → (X ↝ Y) → (X ↝ Y) → X ↝ Y
R ∩ S = wrap λ x y → Λ R x y × Λ S x y

∩-universal-⇒ : {I : Set} {X Y : I → Set} {R S T : X ↝ Y} → R ⊆ S ∩ T → (R ⊆ S) × (R ⊆ T)
∩-universal-⇒ R⊆S∩T = wrap (λ x → wrap (λ y r → proj₁ (modus-ponens-⊆ R⊆S∩T x y r))) , 
                      wrap (λ x → wrap (λ y r → proj₂ (modus-ponens-⊆ R⊆S∩T x y r)))

∩-universal-⇐ : {I : Set} {X Y : I → Set} {R S T : X ↝ Y} → R ⊆ S → R ⊆ T → R ⊆ S ∩ T
∩-universal-⇐ R⊆S R⊆T = wrap λ x → wrap λ y r → modus-ponens-⊆ R⊆S x y r , modus-ponens-⊆ R⊆T x y r