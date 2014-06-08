-- Definition of right-division of componentwise relations.

module Relation.Division where

open import Relation

open import Data.Product using (Σ; Σ-syntax; _,_)

infixr 5 _/_

_/_ : {I : Set} {X Y Z : I → Set} → (X ↝ Y) → (X ↝ Z) → Z ↝ Y
wrap R / wrap S = wrap λ i z y → (∀ x → S i x z → R i x y)

/-universal-⇒ : {I : Set} {X Y Z : I → Set} {T : Z ↝ Y} {R : X ↝ Y} {S : X ↝ Z} → T ⊆ R / S → T • S ⊆ R
/-universal-⇒ T⊆R/S = wrap λ i → wrap λ { x y (z , s , t) → modus-ponens-⊆ T⊆R/S i z y t x s }

/-universal-⇐ : {I : Set} {X Y Z : I → Set} {T : Z ↝ Y} {R : X ↝ Y} {S : X ↝ Z} → T • S ⊆ R → T ⊆ R / S
/-universal-⇐ T•S⊆R = wrap λ i → wrap λ z y t x s → modus-ponens-⊆ T•S⊆R i x y (z , s , t)
