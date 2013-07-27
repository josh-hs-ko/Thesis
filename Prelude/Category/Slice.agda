-- Definition of slice categories.

module Prelude.Category.Slice where

open import Prelude.Category

open import Level
open import Function using ()
open import Data.Product using (Σ; _,_)
open import Relation.Binary using (module Setoid)
import Relation.Binary.EqReasoning as EqReasoning

open Functor


record Slice {ℓ₀ ℓ₁ ℓ₂ : Level} (C : Category {ℓ₀} {ℓ₁} {ℓ₂}) (B : Category.Object C) : Set (ℓ₀ ⊔ ℓ₁) where
  constructor slice
  open Category C
  field
    T : Object
    s : T ==> B

record SliceMorphism {ℓ₀ ℓ₁ ℓ₂ : Level} (C : Category {ℓ₀} {ℓ₁} {ℓ₂}) (B : Category.Object C) (s t : Slice C B) : Set (ℓ₁ ⊔ ℓ₂) where
  constructor sliceMorphism
  open Category C
  field
    m : Slice.T s ==> Slice.T t
    triangle : Slice.s t · m ≈ Slice.s s

two-triangles :
  {ℓ₀ ℓ₁ ℓ₂ : Level} (C : Category {ℓ₀} {ℓ₁} {ℓ₂}) (B : Category.Object C) →
  {s t u : Slice C B} (f : SliceMorphism C B t u) (g : SliceMorphism C B s t) →
  Category._≈_ C (Category._·_ C (Slice.s u) (Category._·_ C (SliceMorphism.m f) (SliceMorphism.m g))) (Slice.s s)
two-triangles C B {s} {t} {u} f g =
  begin
    Slice.s u · (SliceMorphism.m f · SliceMorphism.m g)
      ≈⟨ Setoid.sym setoid (assoc (Slice.s u) (SliceMorphism.m f) (SliceMorphism.m g)) ⟩
    (Slice.s u · SliceMorphism.m f) · SliceMorphism.m g
      ≈⟨ cong-r (SliceMorphism.m g) (SliceMorphism.triangle f) ⟩
    Slice.s t · SliceMorphism.m g
      ≈⟨ SliceMorphism.triangle g ⟩
    Slice.s s
  ∎
  where open Category C
        setoid = Morphism (Slice.T s) B
        open EqReasoning setoid

SliceCategory : {ℓ₀ ℓ₁ ℓ₂ : Level} (C : Category {ℓ₀} {ℓ₁} {ℓ₂}) (B : Category.Object C) → Category
SliceCategory C B =
  record { Object   = Slice C B
         ; Morphism = λ { s t → record { Carrier = SliceMorphism C B s t
                                       ; _≈_ = λ { f g → SliceMorphism.m f ≈ SliceMorphism.m g }
                                       ; isEquivalence =
                                           record { refl  = Setoid.refl (Morphism (Slice.T s) (Slice.T t))
                                                  ; sym   = Setoid.sym (Morphism (Slice.T s) (Slice.T t))
                                                  ; trans = Setoid.trans (Morphism (Slice.T s) (Slice.T t)) } } }
         ; _·_ = λ f g → record { m = SliceMorphism.m f · SliceMorphism.m g; triangle = two-triangles C B f g }
         ; id  = λ {s} → record { m = id; triangle = id-r (Slice.s s) }
         ; id-l   = λ f → id-l (SliceMorphism.m f)
         ; id-r   = λ f → id-r (SliceMorphism.m f)
         ; assoc  = λ f g h → assoc (SliceMorphism.m f) (SliceMorphism.m g) (SliceMorphism.m h)
         ; cong-l = λ h → cong-l (SliceMorphism.m h)
         ; cong-r = λ h → cong-r (SliceMorphism.m h) }
  where open Category C

SliceU : {ℓ₀ ℓ₁ ℓ₂ : Level} {C : Category {ℓ₀} {ℓ₁} {ℓ₂}} {B : Category.Object C} → Functor (SliceCategory C B) C
SliceU {C = C} =
  record { object   = Slice.T
         ; morphism = SliceMorphism.m
         ; ≈-respecting    = Function.id
         ; id-preserving   = λ {s} → Setoid.refl (Category.Morphism C (Slice.T s) (Slice.T s))
         ; comp-preserving = λ {s} {t} {u} f g → Setoid.refl (Category.Morphism C (Slice.T s) (Slice.T u)) }

SliceMap : {ℓ₀ ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ : Level} {C : Category {ℓ₀} {ℓ₁} {ℓ₂}} {D : Category {ℓ₃} {ℓ₄} {ℓ₅}} (F : Functor C D) →
           {B : Category.Object C} → Functor (SliceCategory C B) (SliceCategory D (object F B))
SliceMap {D = D} F {B} =
  record { object   = λ { (slice T s) → slice (object F T) (morphism F s) }
         ; morphism = λ { {s} {t} (sliceMorphism m triangle) →
                          let M = Category.Morphism D (object F (Slice.T s)) (object F B)
                          in  sliceMorphism (morphism F m) (Setoid.trans M (Setoid.sym M (comp-preserving F (Slice.s t) m))
                                                                           (≈-respecting F triangle)) }
         ; ≈-respecting    = ≈-respecting F
         ; id-preserving   = id-preserving F
         ; comp-preserving = λ f g → comp-preserving F (SliceMorphism.m f) (SliceMorphism.m g) }
