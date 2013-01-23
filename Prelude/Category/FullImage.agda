open import Thesis.Prelude.Category
open import Level

module Thesis.Prelude.Category.FullImage
  {ℓ₀ ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ : Level} {C : Category {ℓ₀} {ℓ₁} {ℓ₂}} {D : Category {ℓ₃} {ℓ₄} {ℓ₅}} (F : Functor C D) where

open Category
open Functor

FullImageCategory : Category
FullImageCategory =
  record { Object   = Object C
         ; Morphism = λ X Y → Morphism D (object F X) (object F Y)
         ; _·_ = _·_ D
         ; id  = id D
         ; id-l   = id-l D
         ; id-r   = id-r D
         ; assoc  = assoc D
         ; cong-l = cong-l D
         ; cong-r = cong-r D }

