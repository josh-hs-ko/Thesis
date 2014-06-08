-- A "weak" category of categories, in which morphisms (i.e., functors) are considered equal if they are naturally isomorphic.
-- An equivalence of categories is an isomorphism in this weak category of categories.

module Prelude.Category.WCat where

open import Prelude.Category
open import Prelude.Category.Isomorphism

open import Level
open import Relation.Binary using (module Setoid)

open Category
open Functor


WCat : {ℓ₀ ℓ₁ ℓ₂ : Level} → Category
WCat {ℓ₀} {ℓ₁} {ℓ₂} = record
  { Object   = Category {ℓ₀} {ℓ₁} {ℓ₂}
  ; Morphism = λ C D → IsoSetoid (Funct C D)
  ; _·_ = _⋆_
  ; id  = λ {C} → idF C
  ; id-l   = λ {C} {D} F → record
               { to   = record { comp = λ _ → id D
                               ; naturality = λ {X} {Y} f → Setoid.trans (Morphism D (object F X) (object F Y))
                                                              (id-r D (morphism F f))
                                                              (Setoid.sym (Morphism D (object F X) (object F Y)) (id-l D (morphism F f))) }
               ; from = record { comp = λ _ → id D
                               ; naturality = λ {X} {Y} f → Setoid.trans (Morphism D (object F X) (object F Y))
                                                              (id-r D (morphism F f))
                                                              (Setoid.sym (Morphism D (object F X) (object F Y)) (id-l D (morphism F f))) }
               ; from-to-inverse = λ _ → id-l D (id D)
               ; to-from-inverse = λ _ → id-l D (id D) }
  ; id-r   = λ {C} {D} F → record
               { to   = record { comp = λ _ → id D
                               ; naturality = λ {X} {Y} f → Setoid.trans (Morphism D (object F X) (object F Y))
                                                              (id-r D (morphism F f))
                                                              (Setoid.sym (Morphism D (object F X) (object F Y)) (id-l D (morphism F f))) }
               ; from = record { comp = λ _ → id D
                               ; naturality = λ {X} {Y} f → Setoid.trans (Morphism D (object F X) (object F Y))
                                                              (id-r D (morphism F f))
                                                              (Setoid.sym (Morphism D (object F X) (object F Y)) (id-l D (morphism F f))) }
               ; from-to-inverse = λ _ → id-l D (id D)
               ; to-from-inverse = λ _ → id-l D (id D) }
  ; assoc  = λ {_} {_} {_} {C} F G H → record
               { to   = record { comp = λ _ → id C
                               ; naturality =  λ {X} {Y} f → Setoid.trans (Morphism C _ _)
                                                               (id-r C (morphism F (morphism G (morphism H f))))
                                                               (Setoid.sym (Morphism C _ _) (id-l C (morphism F (morphism G (morphism H f))))) }
               ; from = record { comp = λ _ → id C
                               ; naturality = λ {X} {Y} f → Setoid.trans (Morphism C _ _)
                                                              (id-r C (morphism F (morphism G (morphism H f))))
                                                              (Setoid.sym (Morphism C _ _) (id-l C (morphism F (morphism G (morphism H f))))) }
               ; from-to-inverse = λ _ → id-l C (id C)
               ; to-from-inverse = λ _ → id-l C (id C) }
  ; cong-l = λ {C} {D} {E} {F} {G} H iso → record
               { to   = record { comp = λ X → morphism H (NatTrans.comp (Iso.to iso) X)
                               ; naturality = λ {X} {Y} f → Setoid.trans (Morphism E _ _)
                                                              (Setoid.sym (Morphism E _ _)
                                                                 (comp-preserving H (morphism G f) (NatTrans.comp (Iso.to iso) X)))
                                                              (Setoid.trans (Morphism E _ _)
                                                                 (≈-respecting H (NatTrans.naturality (Iso.to iso) f))
                                                                 (comp-preserving H (NatTrans.comp (Iso.to iso) Y) (morphism F f))) }
               ; from = record { comp = λ X → morphism H (NatTrans.comp (Iso.from iso) X)
                               ; naturality =  λ {X} {Y} f →
                                                 Setoid.trans (Morphism E _ _)
                                                   (Setoid.sym (Morphism E _ _)
                                                      (comp-preserving H (morphism F f) (NatTrans.comp (Iso.from iso) X)))
                                                   (Setoid.trans (Morphism E _ _)
                                                      (≈-respecting H (NatTrans.naturality (Iso.from iso) f))
                                                      (comp-preserving H (NatTrans.comp (Iso.from iso) Y) (morphism G f))) }
  ; from-to-inverse = λ X → Setoid.trans (Morphism E _ _)
                              (Setoid.sym (Morphism E _ _)
                                 (comp-preserving H (NatTrans.comp (Iso.from iso) X) (NatTrans.comp (Iso.to iso) X)))
                              (Setoid.trans (Morphism E _ _) (≈-respecting H (Iso.from-to-inverse iso X)) (id-preserving H))
  ; to-from-inverse = λ X → Setoid.trans (Morphism E _ _)
                              (Setoid.sym (Morphism E _ _)
                                 (comp-preserving H (NatTrans.comp (Iso.to iso) X) (NatTrans.comp (Iso.from iso) X)))
                              (Setoid.trans (Morphism E _ _) (≈-respecting H (Iso.to-from-inverse iso X)) (id-preserving H)) }
  ; cong-r = λ {C} {D} {E} {F} {G} H iso → record
               { to   = record { comp = λ X → NatTrans.comp (Iso.to iso) (object H X)
                               ; naturality = λ f → NatTrans.naturality (Iso.to iso) (morphism H f) }
               ; from = record { comp = λ X → NatTrans.comp (Iso.from iso) (object H X)
                               ; naturality = λ f → NatTrans.naturality (Iso.from iso) (morphism H f) }
               ; from-to-inverse = λ X → Iso.from-to-inverse iso (object H X)
               ; to-from-inverse = λ X → Iso.to-from-inverse iso (object H X) } }

CatEquiv : {ℓ₀ ℓ₁ ℓ₂ : Level} → (C D : Category {ℓ₀} {ℓ₁} {ℓ₂}) → Set (ℓ₀ ⊔ ℓ₁ ⊔ ℓ₂)
CatEquiv = Iso WCat
