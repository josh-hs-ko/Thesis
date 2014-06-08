-- Categorical definition of isomorphisms, parametrised by an underlying category.
-- Isomorphic objects form a setoid and are amenable to equational reasoning.
-- It is proved here that terminal objects are isomorphic.
-- A predicate saying that a morphism is part of an isomorphism is also provided.

open import Prelude.Category
open import Level

module Prelude.Category.Isomorphism {ℓ₀ ℓ₁ ℓ₂ : Level} (C : Category {ℓ₀} {ℓ₁} {ℓ₂}) where

open import Data.Product using (Σ; Σ-syntax; _,_; proj₁; proj₂; _×_)
open import Relation.Binary using (Setoid)
import Relation.Binary.EqReasoning as EqReasoning

open Category C


record Iso (X Y : Object) : Set (ℓ₁ ⊔ ℓ₂) where
  field
    to   : X ==> Y
    from : Y ==> X
    from-to-inverse : from · to ≈ id
    to-from-inverse : to · from ≈ id

private

  sym : {X Y : Object} → Iso X Y → Iso Y X
  sym i = record { to   = Iso.from i
                 ; from = Iso.to i
                 ; from-to-inverse = Iso.to-from-inverse i
                 ; to-from-inverse = Iso.from-to-inverse i }

  module Transitivity {X Y Z : Object} (i : Iso X Y) (j : Iso Y Z) where

    open Iso

    inverse : (to j · to i) · (from i · from j) ≈ id
    inverse =
      begin
        (to j · to i) · (from i · from j)
          ≈⟨ assoc (to j) (to i) (from i · from j) ⟩
        to j · (to i · (from i · from j))
          ≈⟨ Setoid.sym setoid (cong-l (to j) (assoc (to i) (from i) (from j))) ⟩
        to j · ((to i · from i) · from j)
          ≈⟨ cong-l (to j) (cong-r (from j) (to-from-inverse i)) ⟩
        to j · (id · from j)
          ≈⟨ cong-l (to j) (id-l (from j)) ⟩
        to j · from j
          ≈⟨ to-from-inverse j ⟩
        id
      ∎
      where setoid = Morphism Z Z
            open EqReasoning setoid

IsoSetoid : Setoid _ _
IsoSetoid =
  record { Carrier = Object
         ; _≈_ = Iso
         ; isEquivalence =
             record { refl = record { to   = id
                                    ; from = id
                                    ; from-to-inverse = id-l id
                                    ; to-from-inverse = id-l id }
                    ; sym = sym
                    ; trans = λ i j → record { to   = Iso.to j · Iso.to i
                                             ; from = Iso.from i · Iso.from j
                                             ; from-to-inverse = Transitivity.inverse (sym j) (sym i)
                                             ; to-from-inverse = Transitivity.inverse i j } } }

terminal-iso : (X Y : Object) → Terminal C X → Terminal C Y → Iso X Y
terminal-iso X Y tx ty =
  record { to   = proj₁ (ty X)
         ; from = proj₁ (tx Y)
         ; from-to-inverse =
             Setoid.trans (Morphism X X)
               (Setoid.sym (Morphism X X) (proj₂ (tx X) (proj₁ (tx Y) · proj₁ (ty X))))
               (proj₂ (tx X) id)
         ; to-from-inverse =
             Setoid.trans (Morphism Y Y) 
               (Setoid.sym (Morphism Y Y) (proj₂ (ty Y) (proj₁ (ty X) · proj₁ (tx Y))))
               (proj₂ (ty Y) id) }

iso-terminal : (X Y : Object) → Terminal C X → Iso X Y → Terminal C Y
iso-terminal X Y tx i Z =
  let (m , u) = tx Z
  in  Iso.to i · m ,
      λ n → begin
              Iso.to i · m
                ≈⟨ cong-l (Iso.to i) (u (Iso.from i · n)) ⟩
              Iso.to i · (Iso.from i · n)
                ≈⟨ Setoid.sym setoid (assoc (Iso.to i) (Iso.from i) n) ⟩
              (Iso.to i · Iso.from i) · n
                ≈⟨ cong-r n (Iso.to-from-inverse i) ⟩
              id · n
                ≈⟨ id-l n ⟩
              n
            ∎
  where setoid = Morphism Z Y
        open EqReasoning setoid

record PartOfIso {X Y : Object} (to : X ==> Y) : Set (ℓ₁ ⊔ ℓ₂) where
  field
    from : Y ==> X
    from-to-inverse : from · to ≈ id
    to-from-inverse : to · from ≈ id

toIso : {X Y : Object} {to : X ==> Y} → PartOfIso to → Iso X Y
toIso {to = to} iso =
  record { to   = to
         ; from = PartOfIso.from iso
         ; from-to-inverse = PartOfIso.from-to-inverse iso
         ; to-from-inverse = PartOfIso.to-from-inverse iso }
