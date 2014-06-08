-- The forgetful functor from a slice category to its underlying category is pullback-preserving.

module Prelude.Category.Slice.Functor where

open import Prelude.Category
open import Prelude.Category.Slice
open import Prelude.Category.Span
open import Prelude.Category.Pullback

open import Level
open import Data.Product using (Σ; Σ-syntax; _,_; proj₁; proj₂)
open import Relation.Binary using (module Setoid)
import Relation.Binary.EqReasoning as EqReasoning
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open Functor

module PullbackPreserving
  {ℓ₀ ℓ₁ ℓ₂ : Level} {C : Category {ℓ₀} {ℓ₁} {ℓ₂}} {B : Category.Object C} {f : Slice C B} (g h : Slice (SliceCategory C B) f)
  (p : Span (SliceCategory (SliceCategory C B) f) g h) (term-p : Terminal (SpanCategory (SliceCategory (SliceCategory C B) f) g h) p) where

  open Category C

  g' : Slice C (Slice.T f)
  g' = object (SliceMap SliceU) g

  h' : Slice C (Slice.T f)
  h' = object (SliceMap SliceU) h

  p' : Span (SliceCategory C (Slice.T f)) g' h'
  p' = object (SpanMap (SliceMap SliceU)) p

  module Universality (q' : Span (SliceCategory C (Slice.T f)) g' h') where

    Tq : Slice (SliceCategory C B) f
    Tq = slice (slice (Slice.T (Span.M q')) (Slice.s f · Slice.s (Span.M q')))
               (sliceMorphism (Slice.s (Span.M q')) (Setoid.refl (Morphism (Slice.T (Span.M q')) B)))

    Tq-to-g : SliceMorphism (SliceCategory C B) f Tq g
    Tq-to-g =
      sliceMorphism
        (sliceMorphism
          (SliceMorphism.m (Span.l q'))
          (begin
             Slice.s (Slice.T g) · SliceMorphism.m (Span.l q')
               ≈⟨ Setoid.sym setoid (cong-r (SliceMorphism.m (Span.l q')) (SliceMorphism.triangle (Slice.s g))) ⟩
             (Slice.s f · SliceMorphism.m (Slice.s g)) · SliceMorphism.m (Span.l q')
               ≈⟨ assoc (Slice.s f) (SliceMorphism.m (Slice.s g)) (SliceMorphism.m (Span.l q')) ⟩
             Slice.s f · (SliceMorphism.m (Slice.s g) · SliceMorphism.m (Span.l q'))
               ≈⟨ cong-l (Slice.s f) (SliceMorphism.triangle (Span.l q')) ⟩
             Slice.s f · Slice.s (Span.M q')
           ∎))
        (SliceMorphism.triangle (Span.l q'))
      where setoid = Morphism (Slice.T (Span.M q')) B
            open EqReasoning setoid

    Tq-to-h : SliceMorphism (SliceCategory C B) f Tq h
    Tq-to-h =
      sliceMorphism
        (sliceMorphism
          (SliceMorphism.m (Span.r q'))
          (begin
             Slice.s (Slice.T h) · SliceMorphism.m (Span.r q')
               ≈⟨ Setoid.sym setoid (cong-r (SliceMorphism.m (Span.r q')) (SliceMorphism.triangle (Slice.s h))) ⟩
             (Slice.s f · SliceMorphism.m (Slice.s h)) · SliceMorphism.m (Span.r q')
               ≈⟨ assoc (Slice.s f) (SliceMorphism.m (Slice.s h)) (SliceMorphism.m (Span.r q')) ⟩
             Slice.s f · (SliceMorphism.m (Slice.s h) · SliceMorphism.m (Span.r q'))
               ≈⟨ cong-l (Slice.s f) (SliceMorphism.triangle (Span.r q')) ⟩
             Slice.s f · Slice.s (Span.M q')
           ∎))
        (SliceMorphism.triangle (Span.r q'))
      where setoid = Morphism (Slice.T (Span.M q')) B
            open EqReasoning setoid

    q : Span (SliceCategory (SliceCategory C B) f) g h
    q = span Tq Tq-to-g Tq-to-h

    q-to-p : SpanMorphism (SliceCategory (SliceCategory C B) f) g h q p
    q-to-p = proj₁ (term-p q)

    q'-to-p' : SpanMorphism (SliceCategory C (Slice.T f)) g' h' q' p'
    q'-to-p' = spanMorphism
                 (sliceMorphism (SliceMorphism.m (SliceMorphism.m (SpanMorphism.m q-to-p)))
                                (SliceMorphism.triangle (SpanMorphism.m q-to-p)))
                 (SpanMorphism.triangle-l q-to-p)
                 (SpanMorphism.triangle-r q-to-p)

    module Uniqueness (q'-to'-p' : SpanMorphism (SliceCategory C (Slice.T f)) g' h' q' p') where

      m-q-to'-p : SliceMorphism (SliceCategory C B) f (Span.M q) (Span.M p)
      m-q-to'-p =
        sliceMorphism
          (sliceMorphism
            (SliceMorphism.m (SpanMorphism.m q'-to'-p'))
            (begin
               Slice.s (Slice.T (Span.M p)) · SliceMorphism.m (SpanMorphism.m q'-to'-p')
                 ≈⟨ Setoid.sym setoid (cong-r (SliceMorphism.m (SpanMorphism.m q'-to'-p')) (SliceMorphism.triangle (Slice.s (Span.M p)))) ⟩
               (Slice.s f · SliceMorphism.m (Slice.s (Span.M p))) · SliceMorphism.m (SpanMorphism.m q'-to'-p')
                 ≈⟨ assoc (Slice.s f) (SliceMorphism.m (Slice.s (Span.M p))) (SliceMorphism.m (SpanMorphism.m q'-to'-p')) ⟩
               Slice.s f · (SliceMorphism.m (Slice.s (Span.M p)) · SliceMorphism.m (SpanMorphism.m q'-to'-p'))
                 ≈⟨ cong-l (Slice.s f) (SliceMorphism.triangle (SpanMorphism.m q'-to'-p')) ⟩
               Slice.s f · Slice.s (Span.M q')
             ∎))
          (SliceMorphism.triangle (SpanMorphism.m q'-to'-p'))
        where setoid = Morphism (Slice.T (Span.M q')) B
              open EqReasoning setoid

      q-to'-p : SpanMorphism (SliceCategory (SliceCategory C B) f) g h q p
      q-to'-p = spanMorphism m-q-to'-p (SpanMorphism.triangle-l q'-to'-p') (SpanMorphism.triangle-r q'-to'-p')

      uniqueness : SliceMorphism.m (SpanMorphism.m q'-to-p') ≈ SliceMorphism.m (SpanMorphism.m q'-to'-p')
      uniqueness = proj₂ (term-p q) q-to'-p

SliceU-preserves-pullback :
  {ℓ₀ ℓ₁ ℓ₂ : Level} {C : Category {ℓ₀} {ℓ₁} {ℓ₂}} {B : Category.Object C} → Pullback-preserving (SliceU {C = C} {B})
SliceU-preserves-pullback g h p term-p q' =
  PullbackPreserving.Universality.q'-to-p' g h p term-p q' ,
  PullbackPreserving.Universality.Uniqueness.uniqueness g h p term-p q'
