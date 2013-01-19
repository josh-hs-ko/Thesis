module Thesis.Relation.Division where

open import Thesis.Relation

open import Data.Product using (Σ; _,_)

infixr 5 _/_

_/_ : {I : Set} {X Y Z : I → Set} → (X ↝ Y) → (X ↝ Z) → Z ↝ Y
wrap R / wrap S = wrap λ {i} z y → ∀ x → S x z → R x y

/-universal-⇒ : {I : Set} {X Y Z : I → Set} {T : Z ↝ Y} {R : X ↝ Y} {S : X ↝ Z} → T ⊆ R / S → T • S ⊆ R
/-universal-⇒ (wrap T⊆R/S) = wrap λ x → wrap λ y → λ { (z , s , t) → _⊑_.comp (T⊆R/S z) y t x s }

/-universal-⇐ : {I : Set} {X Y Z : I → Set} {T : Z ↝ Y} {R : X ↝ Y} {S : X ↝ Z} → T • S ⊆ R → T ⊆ R / S
/-universal-⇐ (wrap T•S⊆R) = wrap λ z → wrap λ y t x s → _⊑_.comp (T•S⊆R x) y (z , s , t)