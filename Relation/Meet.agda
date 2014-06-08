-- Definition of meet and its componentwise version.

module Relation.Meet where

open import Relation

open import Data.Product using (Σ; Σ-syntax; _,_; proj₁; proj₂; _×_)


_∩⁻_ : {X Y : Set} → (X ↝⁻ Y) → (X ↝⁻ Y) → X ↝⁻ Y
(R ∩⁻ S) x y = R x y × S x y

∩⁻-universal-⇒ : {X Y : Set} {R S T : X ↝⁻ Y} → R ⊆⁻ S ∩⁻ T → (R ⊆⁻ S) × (R ⊆⁻ T)
∩⁻-universal-⇒ R⊆⁻S∩⁻T = wrap (λ x y r → proj₁ (modus-ponens-⊆⁻ R⊆⁻S∩⁻T x y r)) , 
                        wrap (λ x y r → proj₂ (modus-ponens-⊆⁻ R⊆⁻S∩⁻T x y r))

∩⁻-universal-⇐ : {X Y : Set} {R S T : X ↝⁻ Y} → R ⊆⁻ S → R ⊆⁻ T → R ⊆⁻ S ∩⁻ T
∩⁻-universal-⇐ R⊆⁻S R⊆⁻T = wrap λ x y r → modus-ponens-⊆⁻ R⊆⁻S x y r , modus-ponens-⊆⁻ R⊆⁻T x y r

_∩_ : {I : Set} {X Y : I → Set} → (X ↝ Y) → (X ↝ Y) → X ↝ Y
R ∩ S = wrap λ i → (R !!) i ∩⁻ (S !!) i

∩-universal-⇒ : {I : Set} {X Y : I → Set} {R S T : X ↝ Y} → R ⊆ S ∩ T → (R ⊆ S) × (R ⊆ T)
∩-universal-⇒ (wrap R⊆S∩T) = wrap (λ i → proj₁ (∩⁻-universal-⇒ (R⊆S∩T i))) ,  wrap (λ i → proj₂ (∩⁻-universal-⇒ (R⊆S∩T i)))

∩-universal-⇐ : {I : Set} {X Y : I → Set} {R S T : X ↝ Y} → R ⊆ S → R ⊆ T → R ⊆ S ∩ T
∩-universal-⇐ (wrap R⊆S) (wrap R⊆T) = wrap λ i → ∩⁻-universal-⇐ (R⊆S i) (R⊆T i)
