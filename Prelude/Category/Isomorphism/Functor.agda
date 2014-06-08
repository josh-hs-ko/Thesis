-- Isomorphisms are preserved by functors.

open import Prelude.Category
open import Level

module Prelude.Category.Isomorphism.Functor
  {ℓ₀ ℓ₁ ℓ₂ : Level} {C : Category {ℓ₀} {ℓ₁} {ℓ₂}} {ℓ₃ ℓ₄ ℓ₅ : Level} {D : Category {ℓ₃} {ℓ₄} {ℓ₅}} (F : Functor C D) where

open import Prelude.Category.Isomorphism

open import Relation.Binary using (module Setoid)
import Relation.Binary.EqReasoning as EqReasoning

open Category
open Category C using () renaming (_≈_ to _≈C_; _·_ to _·C_)
open Category D using () renaming (_≈_ to _≈D_; _·_ to _·D_)
open Functor

private

  inverse : {X Y : Object C} → (i : Iso C X Y) → morphism F (Iso.to i) ·D morphism F (Iso.from i) ≈D id D
  inverse {X} {Y} i =
    begin
      morphism F to ·D morphism F from
        ≈⟨ Setoid.sym setoid (comp-preserving F to from) ⟩
      morphism F (to ·C from)
        ≈⟨ ≈-respecting F to-from-inverse ⟩
      morphism F (id C)
        ≈⟨ id-preserving F ⟩
      id D
    ∎
    where setoid = Morphism D (object F Y) (object F Y)
          open EqReasoning setoid
          open Iso C i

iso-preserving : {X Y : Object C} → Iso C X Y → Iso D (object F X) (object F Y)
iso-preserving {X} {Y} i =
  record { to   = morphism F to
         ; from = morphism F from
         ; to-from-inverse = inverse i
         ; from-to-inverse = inverse (Setoid.sym (IsoSetoid C) i) }
  where open Iso C i
