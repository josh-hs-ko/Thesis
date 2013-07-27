-- Definition of span categories. Products and product preservation are also defined here.

module Prelude.Category.Span where

open import Prelude.Category
open import Prelude.Category.Isomorphism
open import Prelude.Category.Isomorphism.Functor
open import Prelude.Category.Slice

open import Level
open import Function using (_∘_)
open import Data.Product using (Σ; _,_; proj₁; _×_)
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
         ; Morphism = λ s t → record { Carrier = SpanMorphism C L R s t
                                     ; _≈_ = λ f g → SpanMorphism.m f ≈ SpanMorphism.m g
                                     ; isEquivalence =
                                         record { refl  = Setoid.refl  (Morphism (Span.M s) (Span.M t))
                                                ; sym   = Setoid.sym   (Morphism (Span.M s) (Span.M t))
                                                ; trans = Setoid.trans (Morphism (Span.M s) (Span.M t)) } }
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

Product : {ℓ₀ ℓ₁ ℓ₂ : Level} (C : Category {ℓ₀} {ℓ₁} {ℓ₂}) (L R : Category.Object C) → Category.Object C → Set (ℓ₀ ⊔ ℓ₁ ⊔ ℓ₂)
Product C L R X = Σ (Σ[ s ∶ Span C L R ] Span.M s ≡ X) (Terminal (SpanCategory C L R) ∘ proj₁)
  where open Category C

product-iso : {ℓ₀ ℓ₁ ℓ₂ : Level} (C : Category {ℓ₀} {ℓ₁} {ℓ₂}) (L R : Category.Object C) (X Y : Category.Object C) →
              Product C L R X → Product C L R Y → Iso C X Y
product-iso C L R ._ ._ ((s , refl) , term-s) ((t , refl) , term-t) =
  iso-preserving SpanU (terminal-iso (SpanCategory C L R) s t term-s term-t)

Product-preserving :
  {ℓ₀ ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ : Level} {C : Category {ℓ₀} {ℓ₁} {ℓ₂}} {D : Category {ℓ₃} {ℓ₄} {ℓ₅}} → (F : Functor C D) → Set (ℓ₀ ⊔ ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄ ⊔ ℓ₅)
Product-preserving {C = C} {D = D} F =
  (L R X : Category.Object C) (p : Product C L R X) →
  Terminal (SpanCategory D (object F L) (object F R)) (object (SpanMap F) (proj₁ (proj₁ p)))
