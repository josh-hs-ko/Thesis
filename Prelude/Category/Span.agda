-- Definition of span categories. Products and product preservation are also defined here.

module Prelude.Category.Span where

open import Prelude.Equality
open import Prelude.Category
open import Prelude.Category.Isomorphism
open import Prelude.Category.Isomorphism.Functor
open import Prelude.Category.Slice

open import Level
open import Function using (_∘_)
open import Data.Product using (Σ; Σ-syntax; _,_; proj₁; _×_)
open import Relation.Binary using (module Setoid)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open Functor

record Span {ℓ₀ ℓ₁ ℓ₂ : Level} (C : Category {ℓ₀} {ℓ₁} {ℓ₂}) (L R : Category.Object C) : Set (ℓ₀ ⊔ ℓ₁) where
  constructor span
  open Category C
  field
    M : Object
    l : M ==> L
    r : M ==> R

record SpanMorphism {ℓ₀ ℓ₁ ℓ₂ : Level} (C : Category {ℓ₀} {ℓ₁} {ℓ₂}) (L R : Category.Object C) (s t : Span C L R) : Set (ℓ₁ ⊔ ℓ₂) where
  constructor spanMorphism
  open Category C
  field
    m : Span.M s ==> Span.M t
    triangle-l : Span.l t · m ≈ Span.l s
    triangle-r : Span.r t · m ≈ Span.r s

SpanCategory : {ℓ₀ ℓ₁ ℓ₂ : Level} (C : Category {ℓ₀} {ℓ₁} {ℓ₂}) (L R : Category.Object C) → Category
SpanCategory C L R =
  record { Object   = Span C L R
         ; Morphism = λ s t → toSetoid (Morphism (Span.M s) (Span.M t)) (SpanMorphism.m {_} {_} {_} {C} {L} {R})
         ; _·_ = λ f g → spanMorphism (SpanMorphism.m f · SpanMorphism.m g)
                                      (two-triangles C L (sliceMorphism (SpanMorphism.m f) (SpanMorphism.triangle-l f))
                                                         (sliceMorphism (SpanMorphism.m g) (SpanMorphism.triangle-l g)))
                                      (two-triangles C R (sliceMorphism (SpanMorphism.m f) (SpanMorphism.triangle-r f))
                                                         (sliceMorphism (SpanMorphism.m g) (SpanMorphism.triangle-r g)))
         ; id  = λ {s} → spanMorphism id (id-r (Span.l s)) (id-r (Span.r s))
         ; id-l   = λ f → id-l (SpanMorphism.m f)
         ; id-r   = λ f → id-r (SpanMorphism.m f)
         ; assoc  = λ f g h → assoc (SpanMorphism.m f) (SpanMorphism.m g) (SpanMorphism.m h)
         ; cong-l = λ h → cong-l (SpanMorphism.m h)
         ; cong-r = λ h → cong-r (SpanMorphism.m h) }
  where open Category C

SpanU : {ℓ₀ ℓ₁ ℓ₂ : Level} {C : Category {ℓ₀} {ℓ₁} {ℓ₂}} {L R : Category.Object C} → Functor (SpanCategory C L R) C
SpanU {C = C} =
  record { object   = Span.M
         ; morphism = SpanMorphism.m
         ; ≈-respecting    = Function.id
         ; id-preserving   = λ {s} → Setoid.refl (Category.Morphism C (Span.M s) (Span.M s))
         ; comp-preserving = λ {s} {t} {u} f g → Setoid.refl (Category.Morphism C (Span.M s) (Span.M u)) }

SpanFlip : {ℓ₀ ℓ₁ ℓ₂ : Level} {C : Category {ℓ₀} {ℓ₁} {ℓ₂}} {L R : Category.Object C} → Functor (SpanCategory C L R) (SpanCategory C R L)
SpanFlip {C = C} =
  record { object   = λ s → span (Span.M s) (Span.r s) (Span.l s)
         ; morphism = λ f → spanMorphism (SpanMorphism.m f) (SpanMorphism.triangle-r f) (SpanMorphism.triangle-l f)
         ; ≈-respecting    = Function.id
         ; id-preserving   = λ {s} → Setoid.refl (Category.Morphism C (Span.M s) (Span.M s))
         ; comp-preserving = λ {s} {t} {u} f g → Setoid.refl (Category.Morphism C (Span.M s) (Span.M u)) }

SpanUL : {ℓ₀ ℓ₁ ℓ₂ : Level} {C : Category {ℓ₀} {ℓ₁} {ℓ₂}} {L R : Category.Object C} → Functor (SpanCategory C L R) (SliceCategory C L)
SpanUL {C = C} =
  record { object   = λ s → slice (Span.M s) (Span.l s)
         ; morphism = λ f → sliceMorphism (SpanMorphism.m f) (SpanMorphism.triangle-l f)
         ; ≈-respecting    = Function.id
         ; id-preserving   = λ {s} → Setoid.refl (Category.Morphism C (Span.M s) (Span.M s))
         ; comp-preserving = λ {s} {t} {u} f g → Setoid.refl (Category.Morphism C (Span.M s) (Span.M u)) }

SpanUR : {ℓ₀ ℓ₁ ℓ₂ : Level} {C : Category {ℓ₀} {ℓ₁} {ℓ₂}} {L R : Category.Object C} → Functor (SpanCategory C L R) (SliceCategory C R)
SpanUR = SpanUL ⋆ SpanFlip

SpanMap : {ℓ₀ ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ : Level} {C : Category {ℓ₀} {ℓ₁} {ℓ₂}} {D : Category {ℓ₃} {ℓ₄} {ℓ₅}} (F : Functor C D) →
          {L R : Category.Object C} → Functor (SpanCategory C L R) (SpanCategory D (object F L) (object F R))
SpanMap F =
  record { object   = λ { (span M l r) → span (object F M) (morphism F l) (morphism F r) }
         ; morphism = λ f → spanMorphism (morphism F (SpanMorphism.m f))
                                         (SliceMorphism.triangle (morphism (SliceMap F) (morphism SpanUL f)))
                                         (SliceMorphism.triangle (morphism (SliceMap F) (morphism SpanUR f)))
         ; ≈-respecting    = ≈-respecting F
         ; id-preserving   = id-preserving F
         ; comp-preserving = λ f g → comp-preserving F (SpanMorphism.m f) (SpanMorphism.m g) }

span-mid-iso : {ℓ₀ ℓ₁ ℓ₂ : Level} {C : Category {ℓ₀} {ℓ₁} {ℓ₂}} {L R : Category.Object C} →
               (s : Span C L R) (X : Category.Object C) (i : Iso C (Span.M s) X) → Σ (Span C L R) (Iso (SpanCategory C L R) s)
span-mid-iso {C = C} {L} {R} (span M l r) X i =
  span X (l · Iso.from i) (r · Iso.from i) ,
  record { to   = spanMorphism (Iso.to i)
                               (Setoid.trans (Morphism M L) (assoc l (Iso.from i) (Iso.to i))
                                                            (Setoid.trans (Morphism M L) (cong-l l (Iso.from-to-inverse i)) (id-r l)))
                               (Setoid.trans (Morphism M R) (assoc r (Iso.from i) (Iso.to i))
                                                            (Setoid.trans (Morphism M R) (cong-l r (Iso.from-to-inverse i)) (id-r r)))
         ; from = spanMorphism (Iso.from i) (Setoid.refl (Morphism X L)) (Setoid.refl (Morphism X R))
         ; from-to-inverse = Iso.from-to-inverse i
         ; to-from-inverse = Iso.to-from-inverse i }
  where open Category C

Product : {ℓ₀ ℓ₁ ℓ₂ : Level} (C : Category {ℓ₀} {ℓ₁} {ℓ₂}) (L R : Category.Object C) → Span C L R → Set (ℓ₀ ⊔ ℓ₁ ⊔ ℓ₂)
Product C L R = Terminal (SpanCategory C L R)

product-iso : {ℓ₀ ℓ₁ ℓ₂ : Level} (C : Category {ℓ₀} {ℓ₁} {ℓ₂}) (L R : Category.Object C) (s t : Span C L R) →
              Product C L R s → Product C L R t → Iso C (Span.M s) (Span.M t)
product-iso C L R s t prod-s prod-t = iso-preserving SpanU (terminal-iso (SpanCategory C L R) s t prod-s prod-t)

Product-preserving :
  {ℓ₀ ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ : Level} {C : Category {ℓ₀} {ℓ₁} {ℓ₂}} {D : Category {ℓ₃} {ℓ₄} {ℓ₅}} → (F : Functor C D) → Set (ℓ₀ ⊔ ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄ ⊔ ℓ₅)
Product-preserving {C = C} {D = D} F =
  (L R : Category.Object C) (s : Span C L R) (p : Product C L R s) → Product D (object F L) (object F R) (object (SpanMap F) s)
