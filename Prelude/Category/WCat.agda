module Thesis.Prelude.Category.WCat where

open import Thesis.Prelude.Category
open import Thesis.Prelude.Category.Isomorphism

open import Level
open import Relation.Binary using (Setoid)

-- "weak" category of categories, in which morphisms (i.e., functors) are considered equal if they are naturally isomorphic

WCat : {ℓ₀ ℓ₁ ℓ₂ : Level} → Category
WCat {ℓ₀} {ℓ₁} {ℓ₂} =
  record { Object   = Category {ℓ₀} {ℓ₁} {ℓ₂}
         ; Morphism = λ C D → IsoSetoid (Funct C D)
         ; _·_ = _⋆_
         ; id  = λ {C} → idF C
         ; id-l   = λ {C} {D} F → {!Setoid.refl (IsoSetoid (Funct C D)) {F}!}
         ; id-r   = {!!}
         ; assoc  = {!!}
         ; cong-l = {!!}
         ; cong-r = {!!} }