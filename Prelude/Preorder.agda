-- Converse of preorders, setoids derived from preorders, implication as a preorder, and indirect reasoning combinators.

module Prelude.Preorder where

open import Relation.Binary using (Preorder; module Preorder; Setoid; module Setoid; module IsEquivalence)

open import Level
open import Function using (id; _∘_; flip)
open import Data.Product using (Σ; Σ-syntax; _,_; proj₁; proj₂; _×_; swap)
open import Relation.Binary.PropositionalEquality using (_≡_; refl) renaming (setoid to ≡-Setoid)


ConversePreorder : {c ℓ₁ ℓ₂ : Level} → Preorder c ℓ₁ ℓ₂ → Preorder c ℓ₁ ℓ₂
ConversePreorder preorder =
  record { Carrier = Preorder.Carrier preorder
         ; _≈_ = Preorder._≈_ preorder
         ; _∼_ = flip (Preorder._∼_ preorder)
         ; isPreorder =
             record { isEquivalence = Preorder.isEquivalence preorder
                    ; reflexive = λ eq → Preorder.reflexive preorder (IsEquivalence.sym (Preorder.isEquivalence preorder) eq)
                    ; trans     = flip (Preorder.trans preorder) } }

PreorderSetoid : {c ℓ₁ ℓ₂ : Level} → (preorder : Preorder c ℓ₁ ℓ₂) → Setoid c ℓ₂
PreorderSetoid preorder =
  record { Carrier = Preorder.Carrier preorder
         ; _≈_ = λ x y → Preorder._∼_ preorder x y × Preorder._∼_ preorder y x
         ; isEquivalence =
             record { refl  = Preorder.refl preorder , Preorder.refl preorder
                    ; sym   = swap
                    ; trans = λ { (i∼j , j∼i) (j∼k , k∼j) → Preorder.trans preorder i∼j j∼k , Preorder.trans preorder k∼j j∼i } } }

indirect-reasoning :
  {c ℓ₁ ℓ₂ : Level} → (preorder : Preorder c ℓ₁ ℓ₂) →
  ∀ {x y} → (∀ z → Preorder._∼_ preorder z x → Preorder._∼_ preorder z y) → Preorder._∼_ preorder x y
indirect-reasoning preorder {x} imp = imp x (Preorder.refl preorder)

⇒-Preorder : {ℓ : Level} → Preorder (suc ℓ) (suc ℓ) ℓ
⇒-Preorder {ℓ} =
  record { Carrier = Set ℓ
         ; _≈_ = _≡_
         ; _∼_ = λ A B → (A → B)
         ; isPreorder =
             record { isEquivalence = Setoid.isEquivalence (≡-Setoid _)
                    ; reflexive     = λ { {._} refl → id }
                    ; trans         = λ f g → g ∘ f } }

_⇐_ : {ℓ : Level} → Set ℓ → Set ℓ → Set ℓ
A ⇐ B = B → A

⇐-Preorder : {ℓ : Level} → Preorder (suc ℓ) (suc ℓ) ℓ
⇐-Preorder {ℓ} = ConversePreorder (⇒-Preorder {ℓ})

_⇔_ : {ℓ : Level} → Set ℓ → Set ℓ → Set ℓ
A ⇔ B = (A → B) × (B → A)

⇔-Setoid : {ℓ : Level} → Setoid (suc ℓ) ℓ
⇔-Setoid {ℓ} = PreorderSetoid (⇒-Preorder {ℓ})

indirect-reasoning-⇔ :
  {c ℓ₁ ℓ₂ : Level} → (preorder : Preorder c ℓ₁ ℓ₂) →
  ∀ {x y} → (∀ z → Preorder._∼_ preorder z x ⇔ Preorder._∼_ preorder z y) → Setoid._≈_ (PreorderSetoid preorder) x y
indirect-reasoning-⇔ preorder {x} {y} bi-imp = indirect-reasoning preorder (proj₁ ∘ bi-imp) , indirect-reasoning preorder (proj₂ ∘ bi-imp)
