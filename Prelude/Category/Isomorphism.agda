open import Thesis.Prelude.Category
open import Level

module Thesis.Prelude.Category.Isomorphism {ℓ₀ ℓ₁ ℓ₂ : Level} (C : Category {ℓ₀} {ℓ₁} {ℓ₂}) where

open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary using (Setoid)
import Relation.Binary.EqReasoning as EqReasoning

open Category C


record Iso (X Y : Object) : Set (ℓ₁ ⊔ ℓ₂) where
  field
    to   : X ==> Y
    from : Y ==> X
    to-from-inverse : to · from ≈ id
    from-to-inverse : from · to ≈ id

open Iso

private

  sym : {X Y : Object} → Iso X Y → Iso Y X
  sym i = record { to   = from i
                 ; from = to i
                 ; to-from-inverse = from-to-inverse i
                 ; from-to-inverse = to-from-inverse i }

  module Transitivity {X Y Z : Object} (i : Iso X Y) (j : Iso Y Z) where

    inverse : (to j · to i) · (from i · from j) ≈ id
    inverse =
      begin
        (to j · to i) · (from i · from j)
          ≈⟨ assoc (to j) (to i) (from i · from j) ⟩
        to j · (to i · (from i · from j))
          ≈⟨ cong-l (to j) (Setoid.sym (Morphism Z Y) (assoc (to i) (from i) (from j))) ⟩
        to j · ((to i · from i) · from j)
          ≈⟨ cong-l (to j) (cong-r (from j) (to-from-inverse i)) ⟩
        to j · (id · from j)
          ≈⟨ cong-l (to j) (id-l (from j)) ⟩
        to j · from j
          ≈⟨ to-from-inverse j ⟩
        id
      ∎
      where open EqReasoning (Morphism Z Z)

IsoSetoid : Setoid _ _
IsoSetoid =
  record { Carrier = Object
         ; _≈_ = Iso
         ; isEquivalence =
             record { refl = record { to   = id
                                    ; from = id
                                    ; to-from-inverse = id-l id
                                    ; from-to-inverse = id-l id }
                    ; sym = sym
                    ; trans = λ i j → record { to   = to j · to i
                                             ; from = from i · from j
                                             ; to-from-inverse = Transitivity.inverse i j
                                             ; from-to-inverse = Transitivity.inverse (sym j) (sym i) } } }

terminal-iso : (X Y : Object) → Terminal C X → Terminal C Y → Iso X Y
terminal-iso X Y tx ty =
  record { to   = proj₁ (ty X)
         ; from = proj₁ (tx Y)
         ; to-from-inverse = Setoid.trans (Morphism Y Y) 
                               (Setoid.sym (Morphism Y Y) (proj₂ (ty Y) (proj₁ (ty X) · proj₁ (tx Y))))
                               (proj₂ (ty Y) id)
         ; from-to-inverse = Setoid.trans (Morphism X X)
                               (Setoid.sym (Morphism X X) (proj₂ (tx X) (proj₁ (tx Y) · proj₁ (ty X))))
                               (proj₂ (tx X) id) }
