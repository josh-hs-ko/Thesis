module Thesis.Prelude.Category.Isomorphism.Midpoint where

open import Thesis.Prelude.Equality
open import Thesis.Prelude.Category
open import Thesis.Prelude.Category.Isomorphism
open import Thesis.Prelude.Category.Span

open import Level
open import Data.Product using (Σ; proj₁; proj₂)
open import Relation.Binary using (Setoid)
import Relation.Binary.EqReasoning as EqReasoning

module Half
  {ℓ₀ ℓ₁ ℓ₂ : Level} {C : Category {ℓ₀} {ℓ₁} {ℓ₂}} {X Y Z : Category.Object C} (xy-iso : Iso C X Y)
  (X×Z : Span C X Z) (X×Z-is-Terminal : Terminal (SpanCategory C X Z) X×Z)
  (Y×Z : Span C Y Z) (Y×Z-is-Terminal : Terminal (SpanCategory C Y Z) Y×Z) where

  open Category C
  open Iso C xy-iso

  Y×Z-spans-over-X-Z : Span C X Z
  Y×Z-spans-over-X-Z = span (Span.M Y×Z) (from · Span.l Y×Z) (Span.r Y×Z)

  X×Z-spans-over-Y-Z : Span C Y Z
  X×Z-spans-over-Y-Z = span (Span.M X×Z) (to · Span.l X×Z) (Span.r X×Z)

  to' : SpanMorphism C Y Z X×Z-spans-over-Y-Z Y×Z
  to' = proj₁ (Y×Z-is-Terminal X×Z-spans-over-Y-Z)

  from' : SpanMorphism C X Z Y×Z-spans-over-X-Z X×Z
  from' = proj₁ (X×Z-is-Terminal Y×Z-spans-over-X-Z)

  lemma-l : Span.l X×Z · (SpanMorphism.m from' · SpanMorphism.m to') ≈ Span.l X×Z
  lemma-l =
    begin
      Span.l X×Z · (SpanMorphism.m from' · SpanMorphism.m to')
        ≈⟨ Setoid.sym (Morphism (Span.M X×Z) X) (assoc (Span.l X×Z) (SpanMorphism.m from') (SpanMorphism.m to')) ⟩
      (Span.l X×Z · SpanMorphism.m from') · SpanMorphism.m to'
        ≈⟨ cong-r (SpanMorphism.m to') (SpanMorphism.triangle-l from') ⟩
      (from · Span.l Y×Z) · SpanMorphism.m to'
        ≈⟨ assoc from (Span.l Y×Z) (SpanMorphism.m to') ⟩
      from · (Span.l Y×Z · SpanMorphism.m to')
        ≈⟨ cong-l from (SpanMorphism.triangle-l to') ⟩
      from · (to · Span.l X×Z)
        ≈⟨ Setoid.sym (Morphism (Span.M X×Z) X) (assoc from to (Span.l X×Z)) ⟩
      (from · to) · Span.l X×Z
        ≈⟨ cong-r (Span.l X×Z) from-to-inverse ⟩
      id · Span.l X×Z
        ≈⟨ id-l (Span.l X×Z) ⟩
      Span.l X×Z
    ∎
    where open EqReasoning (Morphism (Span.M X×Z) X)

  lemma-r : Span.r X×Z · (SpanMorphism.m from' · SpanMorphism.m to') ≈ Span.r X×Z
  lemma-r =
    begin
      Span.r X×Z · (SpanMorphism.m from' · SpanMorphism.m to')
        ≈⟨ Setoid.sym (Morphism (Span.M X×Z) Z) (assoc (Span.r X×Z) (SpanMorphism.m from') (SpanMorphism.m to')) ⟩
      (Span.r X×Z · SpanMorphism.m from') · SpanMorphism.m to'
        ≈⟨ cong-r (SpanMorphism.m to') (SpanMorphism.triangle-r from') ⟩
      Span.r Y×Z · SpanMorphism.m to'
        ≈⟨ SpanMorphism.triangle-r to' ⟩
      Span.r X×Z
    ∎
    where open EqReasoning (Morphism (Span.M X×Z) Z)

  inverse : SpanMorphism.m from' · SpanMorphism.m to' ≈ id
  inverse = equal (Category.Morphism (SpanCategory C X Z) X×Z X×Z)
                  (X×Z-is-Terminal X×Z)
                  (spanMorphism (SpanMorphism.m from' · SpanMorphism.m to') lemma-l lemma-r)
                  (Category.id (SpanCategory C X Z))

midpoint-iso :
  {ℓ₀ ℓ₁ ℓ₂ : Level} (C : Category {ℓ₀} {ℓ₁} {ℓ₂}) (X Y Z : Category.Object C) (xy-iso : Iso C X Y)
  (X×Z : Span C X Z) (X×Z-is-Terminal : Terminal (SpanCategory C X Z) X×Z)
  (Y×Z : Span C Y Z) (Y×Z-is-Terminal : Terminal (SpanCategory C Y Z) Y×Z) → Iso C (Span.M X×Z) (Span.M Y×Z)
midpoint-iso C X Y Z xy-iso X×Z X×Z-is-Terminal Y×Z Y×Z-is-Terminal =
  record { to   = SpanMorphism.m (Half.to'   xy-iso X×Z X×Z-is-Terminal Y×Z Y×Z-is-Terminal)
         ; from = SpanMorphism.m (Half.from' xy-iso X×Z X×Z-is-Terminal Y×Z Y×Z-is-Terminal)
         ; to-from-inverse = Half.inverse (Setoid.sym (IsoSetoid C) xy-iso) Y×Z Y×Z-is-Terminal X×Z X×Z-is-Terminal
         ; from-to-inverse = Half.inverse xy-iso X×Z X×Z-is-Terminal Y×Z Y×Z-is-Terminal }