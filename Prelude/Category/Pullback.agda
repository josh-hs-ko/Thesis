-- A pullback is defined to be a terminal object in the category of spans over a slice category.
-- Any two pullback objects are isomorphic.
-- Pullback preservation of functors is also defined.

module Thesis.Prelude.Category.Pullback where

open import Thesis.Prelude.Category
open import Thesis.Prelude.Category.Isomorphism
open import Thesis.Prelude.Category.Isomorphism.Functor
open import Thesis.Prelude.Category.Slice
open import Thesis.Prelude.Category.Span

open import Level
open import Function using (_∘_)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open Category
open Functor


Square : {ℓ₀ ℓ₁ ℓ₂ : Level} (C : Category {ℓ₀} {ℓ₁} {ℓ₂}) {B : Object C} (f g : Slice C B) → Set (ℓ₀ ⊔ ℓ₁ ⊔ ℓ₂)
Square C {B} = Span (SliceCategory C B)

Square-T : {ℓ₀ ℓ₁ ℓ₂ : Level} {C : Category {ℓ₀} {ℓ₁} {ℓ₂}} {B : Object C} {f g : Slice C B} → Square C f g → Object C
Square-T = Slice.T ∘ Span.M

Pullback : {ℓ₀ ℓ₁ ℓ₂ : Level} (C : Category {ℓ₀} {ℓ₁} {ℓ₂}) {B : Object C} (f g : Slice C B) → Square C f g → Set (ℓ₀ ⊔ ℓ₁ ⊔ ℓ₂)
Pullback C {B} = Product (SliceCategory C B)

pullback-iso : {ℓ₀ ℓ₁ ℓ₂ : Level} (C : Category {ℓ₀} {ℓ₁} {ℓ₂}) {B : Object C} (f g : Slice C B) →
               (s t : Square C f g) → Pullback C f g s → Pullback C f g t → Iso C (Square-T s) (Square-T t)
pullback-iso C {B} f g s t pb-s pb-t =
  iso-preserving SliceU (iso-preserving SpanU (terminal-iso (SpanCategory (SliceCategory C B) f g) s t pb-s pb-t))

Pullback-preserving :
  {ℓ₀ ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ : Level} {C : Category {ℓ₀} {ℓ₁} {ℓ₂}} {D : Category {ℓ₃} {ℓ₄} {ℓ₅}} → (F : Functor C D) → Set (ℓ₀ ⊔ ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄ ⊔ ℓ₅)
Pullback-preserving {C = C} {D} F =
  {B : Object C} (f g : Slice C B) (s : Square C f g) → Pullback C f g s →
  Pullback D (object (SliceMap F) f) (object (SliceMap F) g) (object (SpanMap (SliceMap F)) s)
