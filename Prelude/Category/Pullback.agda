-- A pullback is defined to be a terminal object in the category of spans over a slice category.
-- Any two pullback objects are isomorphic.
-- Pullback preservation of functors is also defined.

module Prelude.Category.Pullback where

open import Prelude.Category
open import Prelude.Category.Isomorphism
open import Prelude.Category.Isomorphism.Functor
open import Prelude.Category.Slice
open import Prelude.Category.Span

open import Level
open import Function using (_∘_)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open Category
open Functor


Pullback : {ℓ₀ ℓ₁ ℓ₂ : Level} (C : Category {ℓ₀} {ℓ₁} {ℓ₂}) {B : Object C} (f g : Slice C B) → Object C → Set (ℓ₀ ⊔ ℓ₁ ⊔ ℓ₂)
Pullback C {B} f g X = Σ (Σ[ s ∶ Span (SliceCategory C B) f g ] Slice.T (Span.M s) ≡ X) (Terminal (SpanCategory (SliceCategory C B) f g) ∘ proj₁)

pullback-iso : {ℓ₀ ℓ₁ ℓ₂ : Level} (C : Category {ℓ₀} {ℓ₁} {ℓ₂}) {B : Object C} (f g : Slice C B) →
               (X Y : Object C) → Pullback C f g X → Pullback C f g Y → Iso C X Y
pullback-iso C {B} f g ._ ._ ((s , refl) , ps) ((t , refl) , pt) =
  iso-preserving SliceU (iso-preserving SpanU (terminal-iso (SpanCategory (SliceCategory C B) f g) s t ps pt))

Pullback-preserving :
  {ℓ₀ ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ : Level} {C : Category {ℓ₀} {ℓ₁} {ℓ₂}} {D : Category {ℓ₃} {ℓ₄} {ℓ₅}} → (F : Functor C D) → Set (ℓ₀ ⊔ ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄ ⊔ ℓ₅)
Pullback-preserving {C = C} {D} F =
  {B : Object C} (f g : Slice C B) (X : Object C) (p : Pullback C f g X) →
  Terminal (SpanCategory (SliceCategory D (object F B)) (object (SliceMap F) f) (object (SliceMap F) g))
           (object (SpanMap (SliceMap F)) (proj₁ (proj₁ p)))
