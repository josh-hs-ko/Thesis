module Thesis.Prelude.Category.Equivalence where

open import Thesis.Prelude.Category
open import Thesis.Prelude.Category.Isomorphism

open import Level


record CategoryEquivalence {ℓ₀ ℓ₁ ℓ₂ : Level} (C D : Category {ℓ₀} {ℓ₁} {ℓ₂}) : Set (ℓ₀ ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    to   : Functor C D
    from : Functor D C
    to-from-inverse : Iso (Funct D D) (to ⋆ from) (idF D)
    from-to-inverse : Iso (Funct C C) (from ⋆ to) (idF C)

