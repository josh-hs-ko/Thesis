module Thesis.Prelude.Implication where

open import Level
open import Function using (id; _∘_)
open import Relation.Binary using (Setoid; Preorder)
open import Relation.Binary.PropositionalEquality using (_≡_; refl) renaming (setoid to ≡-Setoid)

⇐-Preorder : {ℓ : Level} → Preorder _ _ _
⇐-Preorder {ℓ} =
  record { Carrier = Set ℓ
         ; _≈_ = _≡_
         ; _∼_ = λ A B → (B → A)
         ; isPreorder =
             record { isEquivalence = Setoid.isEquivalence (≡-Setoid _)
                    ; reflexive     = λ { {._} refl → id }
                    ; trans         = λ f g → f ∘ g } }