-- A pullback is defined to be a terminal object in the category of spans over a slice category.
-- Any two pullback objects are isomorphic.
-- Pullback preservation and reflection of functors are also defined.
-- A functor preserves pullback if it preserves a particular pullback.
-- Composition of two pullback-reflecting functors is also pullback-reflecting.

module Prelude.Category.Pullback where

open import Prelude.Category
open import Prelude.Category.Isomorphism
open import Prelude.Category.Isomorphism.Functor
open import Prelude.Category.Slice
open import Prelude.Category.Span

open import Level
open import Function using (_∘_)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary using (module Setoid)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import Relation.Binary.EqReasoning as EqReasoning

open Category
open Functor


SquareCategory : {ℓ₀ ℓ₁ ℓ₂ : Level} (C : Category {ℓ₀} {ℓ₁} {ℓ₂}) {B : Object C} (f g : Slice C B) → Category
SquareCategory C {B} f g = SpanCategory (SliceCategory C B) f g

Square : {ℓ₀ ℓ₁ ℓ₂ : Level} (C : Category {ℓ₀} {ℓ₁} {ℓ₂}) {B : Object C} (f g : Slice C B) → Set (ℓ₀ ⊔ ℓ₁ ⊔ ℓ₂)
Square C f g = Object (SquareCategory C f g)

SquareMorphism : {ℓ₀ ℓ₁ ℓ₂ : Level} (C : Category {ℓ₀} {ℓ₁} {ℓ₂}) {B : Object C} (f g : Slice C B) (q r : Square C f g) → Set (ℓ₁ ⊔ ℓ₂)
SquareMorphism C f g q r = Setoid.Carrier (Morphism (SquareCategory C f g) q r)

Square-T : {ℓ₀ ℓ₁ ℓ₂ : Level} {C : Category {ℓ₀} {ℓ₁} {ℓ₂}} {B : Object C} {f g : Slice C B} → Square C f g → Object C
Square-T = Slice.T ∘ Span.M

SquareMorphism-m : {ℓ₀ ℓ₁ ℓ₂ : Level} {C : Category {ℓ₀} {ℓ₁} {ℓ₂}} {B : Object C} {f g : Slice C B} {q r : Square C f g} →
                   SquareMorphism C f g q r → Setoid.Carrier (Morphism C (Square-T q) (Square-T r))
SquareMorphism-m = SliceMorphism.m ∘ SpanMorphism.m

SquareMap : {ℓ₀ ℓ₁ ℓ₂ : Level} {C : Category {ℓ₀} {ℓ₁} {ℓ₂}} {B : Object C} {f g : Slice C B} {ℓ₃ ℓ₄ ℓ₅ : Level} {D : Category {ℓ₃} {ℓ₄} {ℓ₅}}
            (F : Functor C D) → Functor (SquareCategory C f g) (SquareCategory D (Functor.object (SliceMap F) f) (Functor.object (SliceMap F) g))
SquareMap F = SpanMap (SliceMap F)

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

particular-pullback-preservation :
  {ℓ₀ ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ : Level} {C : Category {ℓ₀} {ℓ₁} {ℓ₂}} {D : Category {ℓ₃} {ℓ₄} {ℓ₅}} (F : Functor C D) →
  ({B : Object C} (f g : Slice C B) → Σ[ s ∶ Square C f g ] Pullback C f g s × Pullback D (object (SliceMap F) f) (object (SliceMap F) g) (object (SquareMap F) s)) →
  Pullback-preserving F
particular-pullback-preservation {C = C} {D} F particular {B} f g s' ps' =
  let s   = proj₁ (particular f g)
  in  iso-terminal (SquareCategory D (object (SliceMap F) f) (object (SliceMap F) g))
                   (object (SquareMap F) s)
                   (object (SquareMap F) s')
                   (proj₂ (proj₂ (particular f g)))
                   (iso-preserving (SquareMap F) (terminal-iso (SquareCategory C f g) s s' (proj₁ (proj₂ (particular f g))) ps'))

Pullback-reflecting :
  {ℓ₀ ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ : Level} {C : Category {ℓ₀} {ℓ₁} {ℓ₂}} {D : Category {ℓ₃} {ℓ₄} {ℓ₅}} → (F : Functor C D) → Set (ℓ₀ ⊔ ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄ ⊔ ℓ₅)
Pullback-reflecting {C = C} {D} F =
  {B : Object C} (f g : Slice C B) (s : Square C f g) →
  Pullback D (object (SliceMap F) f) (object (SliceMap F) g) (object (SpanMap (SliceMap F)) s) → Pullback C f g s

Pullback-reflecting-comp :
  {ℓ₀ ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ ℓ₆ ℓ₇ ℓ₈ : Level}
  {C : Category {ℓ₀} {ℓ₁} {ℓ₂}} {D : Category {ℓ₃} {ℓ₄} {ℓ₅}}  {E : Category {ℓ₆} {ℓ₇} {ℓ₈}} →
  (F : Functor D E) → Pullback-reflecting F → (G : Functor C D) → Pullback-reflecting G → Pullback-reflecting (F ⋆ G)
Pullback-reflecting-comp F prF G prG f g s p =
  prG f g s
    (prF (object (SliceMap G) f) (object (SliceMap G) g) (object (SquareMap G) s)
      (λ s' → spanMorphism (SpanMorphism.m (proj₁ (p s'))) (SpanMorphism.triangle-l (proj₁ (p s'))) (SpanMorphism.triangle-r (proj₁ (p s'))) ,
              λ { (spanMorphism m l r) → proj₂ (p s') (spanMorphism m l r) }))
