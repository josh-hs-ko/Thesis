-- *The Midpoint Lemma:*
-- Let X, Y, Z be objects of a category C, and X × Y, X × Z, Y × Z, and (X × Y) × Z be products.
-- Then (X × Y) × Z is a pullback of the projections X × Z → Z and Y × Z → Z.

open import Prelude.Category
open import Prelude.Category.Slice
open import Prelude.Category.Span
open import Level

module Prelude.Category.Pullback.Midpoint
  {ℓ₀ ℓ₁ ℓ₂ : Level} (C : Category {ℓ₀} {ℓ₁} {ℓ₂}) (X Y Z : Category.Object C)
  (X×Y : Span C X Y) (X×Y-is-Terminal : Terminal (SpanCategory C X Y) X×Y)
  (X×Z : Span C X Z) (X×Z-is-Terminal : Terminal (SpanCategory C X Z) X×Z) 
  (Y×Z : Span C Y Z) (Y×Z-is-Terminal : Terminal (SpanCategory C Y Z) Y×Z)
  (X×Y×Z : Span C (Span.M X×Y) Z) (X×Y×Z-is-Terminal : Terminal (SpanCategory C (Span.M X×Y) Z) X×Y×Z) where

open import Prelude.Equality
open import Prelude.Category.Pullback

open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary using (module Setoid)
import Relation.Binary.EqReasoning as EqReasoning
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open Category C
open Functor


f : Slice C Z
f = object SpanUR X×Z

g : Slice C Z
g = object SpanUR Y×Z

X×Y×Z-spans-over-X-Z : Span C X Z
X×Y×Z-spans-over-X-Z = span (Span.M X×Y×Z) (Span.l X×Y · Span.l X×Y×Z) (Span.r X×Y×Z)

X×Y×Z-spans-over-Y-Z : Span C Y Z
X×Y×Z-spans-over-Y-Z = span (Span.M X×Y×Z) (Span.r X×Y · Span.l X×Y×Z) (Span.r X×Y×Z)

X×Y×Z-to-X×Z : SpanMorphism C X Z X×Y×Z-spans-over-X-Z X×Z
X×Y×Z-to-X×Z = proj₁ (X×Z-is-Terminal X×Y×Z-spans-over-X-Z)

X×Y×Z-to-Y×Z : SpanMorphism C Y Z X×Y×Z-spans-over-Y-Z Y×Z
X×Y×Z-to-Y×Z = proj₁ (Y×Z-is-Terminal X×Y×Z-spans-over-Y-Z)

X×Y×Z-pullback : Span (SliceCategory C Z) f g
X×Y×Z-pullback = span (object SpanUR X×Y×Z)
                      (sliceMorphism (SpanMorphism.m X×Y×Z-to-X×Z) (SpanMorphism.triangle-r X×Y×Z-to-X×Z))
                      (sliceMorphism (SpanMorphism.m X×Y×Z-to-Y×Z) (SpanMorphism.triangle-r X×Y×Z-to-Y×Z))

module Universality (W : Span (SliceCategory C Z) f g) where

  W-spans-over-X-Y : Span C X Y
  W-spans-over-X-Y = span (Slice.T (Span.M W)) (Span.l X×Z · SliceMorphism.m (Span.l W)) (Span.l Y×Z · SliceMorphism.m (Span.r W))

  W-to-X×Y : SpanMorphism C X Y W-spans-over-X-Y X×Y
  W-to-X×Y = proj₁ (X×Y-is-Terminal W-spans-over-X-Y)

  W-spans-over-X×Y-Z : Span C (Span.M X×Y) Z
  W-spans-over-X×Y-Z = span (Slice.T (Span.M W)) (SpanMorphism.m W-to-X×Y) (Slice.s (Span.M W))

  W-to-X×Y×Z' : SpanMorphism C (Span.M X×Y) Z W-spans-over-X×Y-Z X×Y×Z
  W-to-X×Y×Z' = proj₁ (X×Y×Z-is-Terminal W-spans-over-X×Y-Z)

  lemma-X×Z-X : Span.l X×Z · (SpanMorphism.m X×Y×Z-to-X×Z · SpanMorphism.m W-to-X×Y×Z') ≈ Span.l X×Z · SliceMorphism.m (Span.l W)
  lemma-X×Z-X =
    begin
      Span.l X×Z · (SpanMorphism.m X×Y×Z-to-X×Z · SpanMorphism.m W-to-X×Y×Z')
        ≈⟨ Setoid.sym setoid (assoc (Span.l X×Z) (SpanMorphism.m X×Y×Z-to-X×Z) (SpanMorphism.m W-to-X×Y×Z')) ⟩
      (Span.l X×Z · SpanMorphism.m X×Y×Z-to-X×Z) · SpanMorphism.m W-to-X×Y×Z'
        ≈⟨ cong-r (SpanMorphism.m W-to-X×Y×Z') (SpanMorphism.triangle-l X×Y×Z-to-X×Z) ⟩
      (Span.l X×Y · Span.l X×Y×Z) · SpanMorphism.m W-to-X×Y×Z'
        ≈⟨ assoc (Span.l X×Y) (Span.l X×Y×Z) (SpanMorphism.m W-to-X×Y×Z') ⟩
      Span.l X×Y · (Span.l X×Y×Z · SpanMorphism.m W-to-X×Y×Z')
        ≈⟨ cong-l (Span.l X×Y) (SpanMorphism.triangle-l W-to-X×Y×Z') ⟩
      Span.l X×Y · SpanMorphism.m W-to-X×Y
        ≈⟨ SpanMorphism.triangle-l W-to-X×Y ⟩
      Span.l X×Z · SliceMorphism.m (Span.l W)
    ∎
    where setoid = Morphism (Slice.T (Span.M W)) X
          open EqReasoning setoid

  lemma-Y×Z-Y : Span.l Y×Z · (SpanMorphism.m X×Y×Z-to-Y×Z · SpanMorphism.m W-to-X×Y×Z') ≈ Span.l Y×Z · SliceMorphism.m (Span.r W)
  lemma-Y×Z-Y =
    begin
      Span.l Y×Z · (SpanMorphism.m X×Y×Z-to-Y×Z · SpanMorphism.m W-to-X×Y×Z')
        ≈⟨ Setoid.sym setoid (assoc (Span.l Y×Z) (SpanMorphism.m X×Y×Z-to-Y×Z) (SpanMorphism.m W-to-X×Y×Z')) ⟩
      (Span.l Y×Z · SpanMorphism.m X×Y×Z-to-Y×Z) · SpanMorphism.m W-to-X×Y×Z'
        ≈⟨ cong-r (SpanMorphism.m W-to-X×Y×Z') (SpanMorphism.triangle-l X×Y×Z-to-Y×Z) ⟩
      (Span.r X×Y · Span.l X×Y×Z) · SpanMorphism.m W-to-X×Y×Z'
        ≈⟨ assoc (Span.r X×Y) (Span.l X×Y×Z) (SpanMorphism.m W-to-X×Y×Z') ⟩
      Span.r X×Y · (Span.l X×Y×Z · SpanMorphism.m W-to-X×Y×Z')
        ≈⟨ cong-l (Span.r X×Y) (SpanMorphism.triangle-l W-to-X×Y×Z') ⟩
      Span.r X×Y · SpanMorphism.m W-to-X×Y
        ≈⟨ SpanMorphism.triangle-r W-to-X×Y ⟩
      Span.l Y×Z · SliceMorphism.m (Span.r W)
    ∎
    where setoid = Morphism (Slice.T (Span.M W)) Y
          open EqReasoning setoid

  lemma-X×Z-Z : Span.r X×Z · (SpanMorphism.m X×Y×Z-to-X×Z · SpanMorphism.m W-to-X×Y×Z') ≈ Span.r X×Z · SliceMorphism.m (Span.l W)
  lemma-X×Z-Z =
    begin
      Span.r X×Z · (SpanMorphism.m X×Y×Z-to-X×Z · SpanMorphism.m W-to-X×Y×Z')
        ≈⟨ Setoid.sym setoid (assoc (Span.r X×Z) (SpanMorphism.m X×Y×Z-to-X×Z) (SpanMorphism.m W-to-X×Y×Z')) ⟩
      (Span.r X×Z · SpanMorphism.m X×Y×Z-to-X×Z) · SpanMorphism.m W-to-X×Y×Z'
        ≈⟨ cong-r (SpanMorphism.m W-to-X×Y×Z') (SpanMorphism.triangle-r X×Y×Z-to-X×Z) ⟩
      Span.r X×Y×Z · SpanMorphism.m W-to-X×Y×Z'
        ≈⟨ SpanMorphism.triangle-r W-to-X×Y×Z' ⟩
      Slice.s (Span.M W)
        ≈⟨ Setoid.sym setoid (SliceMorphism.triangle (Span.l W)) ⟩
      Span.r X×Z · SliceMorphism.m (Span.l W)
    ∎
    where setoid = Morphism (Slice.T (Span.M W)) Z
          open EqReasoning setoid

  lemma-Y×Z-Z : Span.r Y×Z · (SpanMorphism.m X×Y×Z-to-Y×Z · SpanMorphism.m W-to-X×Y×Z') ≈ Span.r Y×Z · SliceMorphism.m (Span.r W)
  lemma-Y×Z-Z =
    begin
      Span.r Y×Z · (SpanMorphism.m X×Y×Z-to-Y×Z · SpanMorphism.m W-to-X×Y×Z')
        ≈⟨ Setoid.sym setoid (assoc (Span.r Y×Z) (SpanMorphism.m X×Y×Z-to-Y×Z) (SpanMorphism.m W-to-X×Y×Z')) ⟩
      (Span.r Y×Z · SpanMorphism.m X×Y×Z-to-Y×Z) · SpanMorphism.m W-to-X×Y×Z'
        ≈⟨ cong-r (SpanMorphism.m W-to-X×Y×Z') (SpanMorphism.triangle-r X×Y×Z-to-Y×Z) ⟩
      Span.r X×Y×Z · SpanMorphism.m W-to-X×Y×Z'
        ≈⟨ SpanMorphism.triangle-r W-to-X×Y×Z' ⟩
      Slice.s (Span.M W)
        ≈⟨ Setoid.sym setoid (SliceMorphism.triangle (Span.r W)) ⟩
      Span.r Y×Z · SliceMorphism.m (Span.r W)
    ∎
    where setoid = Morphism (Slice.T (Span.M W)) Z
          open EqReasoning setoid

  W-to-X×Y×Z : SpanMorphism (SliceCategory C Z) f g W X×Y×Z-pullback
  W-to-X×Y×Z =
    spanMorphism
      (sliceMorphism (SpanMorphism.m W-to-X×Y×Z') (SpanMorphism.triangle-r W-to-X×Y×Z'))
      (let W-spans-over-X-Z =
             span (Slice.T (Span.M W)) (Span.l X×Z · SliceMorphism.m (Span.l W)) (Span.r X×Z · SliceMorphism.m (Span.l W))
       in  equal (Category.Morphism (SpanCategory C X Z) W-spans-over-X-Z X×Z)
             (X×Z-is-Terminal W-spans-over-X-Z)
             (spanMorphism (SpanMorphism.m X×Y×Z-to-X×Z · SpanMorphism.m W-to-X×Y×Z') lemma-X×Z-X lemma-X×Z-Z)
             (spanMorphism (SliceMorphism.m (Span.l W)) (Setoid.refl (Morphism (Slice.T (Span.M W)) X))
                                                        (Setoid.refl (Morphism (Slice.T (Span.M W)) Z))))
      (let W-spans-over-Y-Z =
             span (Slice.T (Span.M W)) (Span.l Y×Z · SliceMorphism.m (Span.r W)) (Span.r Y×Z · SliceMorphism.m (Span.r W))
       in  equal (Category.Morphism (SpanCategory C Y Z) W-spans-over-Y-Z Y×Z)
             (Y×Z-is-Terminal W-spans-over-Y-Z)
             (spanMorphism (SpanMorphism.m X×Y×Z-to-Y×Z · SpanMorphism.m W-to-X×Y×Z') lemma-Y×Z-Y lemma-Y×Z-Z)
             (spanMorphism (SliceMorphism.m (Span.r W)) (Setoid.refl (Morphism (Slice.T (Span.M W)) Y))
                                                        (Setoid.refl (Morphism (Slice.T (Span.M W)) Z))))

  module Uniqueness (m' : SpanMorphism (SliceCategory C Z) f g W X×Y×Z-pullback) where

    lemma-X×Y-X : Span.l X×Y · (Span.l X×Y×Z · SliceMorphism.m (SpanMorphism.m m')) ≈ Span.l X×Z · SliceMorphism.m (Span.l W)
    lemma-X×Y-X =
      begin
        Span.l X×Y · (Span.l X×Y×Z · SliceMorphism.m (SpanMorphism.m m'))
          ≈⟨ Setoid.sym setoid (assoc (Span.l X×Y) (Span.l X×Y×Z) (SliceMorphism.m (SpanMorphism.m m'))) ⟩
        (Span.l X×Y · Span.l X×Y×Z) · SliceMorphism.m (SpanMorphism.m m')
          ≈⟨ Setoid.sym setoid (cong-r (SliceMorphism.m (SpanMorphism.m m')) (SpanMorphism.triangle-l X×Y×Z-to-X×Z)) ⟩
        (Span.l X×Z · SpanMorphism.m X×Y×Z-to-X×Z) · SliceMorphism.m (SpanMorphism.m m')
          ≈⟨ assoc (Span.l X×Z) (SpanMorphism.m X×Y×Z-to-X×Z) (SliceMorphism.m (SpanMorphism.m m')) ⟩
        Span.l X×Z · (SpanMorphism.m X×Y×Z-to-X×Z · SliceMorphism.m (SpanMorphism.m m'))
          ≈⟨ cong-l (Span.l X×Z) (SpanMorphism.triangle-l m') ⟩
        Span.l X×Z · SliceMorphism.m (Span.l W)
      ∎
      where setoid = Morphism (Slice.T (Span.M W)) X
            open EqReasoning setoid

    lemma-X×Y-Y : Span.r X×Y · (Span.l X×Y×Z · SliceMorphism.m (SpanMorphism.m m')) ≈ Span.l Y×Z · SliceMorphism.m (Span.r W)
    lemma-X×Y-Y =
      begin
        Span.r X×Y · (Span.l X×Y×Z · SliceMorphism.m (SpanMorphism.m m'))
          ≈⟨ Setoid.sym setoid (assoc (Span.r X×Y) (Span.l X×Y×Z) (SliceMorphism.m (SpanMorphism.m m'))) ⟩
        (Span.r X×Y · Span.l X×Y×Z) · SliceMorphism.m (SpanMorphism.m m')
          ≈⟨ Setoid.sym setoid (cong-r (SliceMorphism.m (SpanMorphism.m m')) (SpanMorphism.triangle-l X×Y×Z-to-Y×Z)) ⟩
        (Span.l Y×Z · SpanMorphism.m X×Y×Z-to-Y×Z) · SliceMorphism.m (SpanMorphism.m m')
          ≈⟨ assoc (Span.l Y×Z) (SpanMorphism.m X×Y×Z-to-Y×Z) (SliceMorphism.m (SpanMorphism.m m')) ⟩
        Span.l Y×Z · (SpanMorphism.m X×Y×Z-to-Y×Z · SliceMorphism.m (SpanMorphism.m m'))
          ≈⟨ cong-l (Span.l Y×Z) (SpanMorphism.triangle-r m') ⟩
        Span.l Y×Z · SliceMorphism.m (Span.r W)
      ∎
      where setoid = Morphism (Slice.T (Span.M W)) Y
            open EqReasoning setoid

    uniqueness : SliceMorphism.m (SpanMorphism.m W-to-X×Y×Z) ≈ SliceMorphism.m (SpanMorphism.m m')
    uniqueness =
      proj₂ (X×Y×Z-is-Terminal W-spans-over-X×Y-Z)
        (spanMorphism (SliceMorphism.m (SpanMorphism.m m'))
                      (Setoid.sym (Morphism (Slice.T (Span.M W)) (Span.M X×Y))
                        (proj₂ (X×Y-is-Terminal W-spans-over-X-Y)
                           (spanMorphism (Span.l X×Y×Z · SliceMorphism.m (SpanMorphism.m m')) lemma-X×Y-X lemma-X×Y-Y)))
                      (SliceMorphism.triangle (SpanMorphism.m m')))

midpoint-pullback : Pullback C f g (Span.M X×Y×Z)
midpoint-pullback =
  (span (object SpanUR X×Y×Z)
        (sliceMorphism (SpanMorphism.m X×Y×Z-to-X×Z) (SpanMorphism.triangle-r X×Y×Z-to-X×Z))
        (sliceMorphism (SpanMorphism.m X×Y×Z-to-Y×Z) (SpanMorphism.triangle-r X×Y×Z-to-Y×Z)) , refl) ,
  (λ W → Universality.W-to-X×Y×Z W , Universality.Uniqueness.uniqueness W)
