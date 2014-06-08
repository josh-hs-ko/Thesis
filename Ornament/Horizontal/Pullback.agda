-- `Shape : Functor ḞḢTrans Fam` and `Erase : Functor Ōrn ḞḢTrans` reflect pullbacks.
-- This file can take a long time to typecheck.

module Ornament.Horizontal.Pullback where

open import Prelude.Category
open import Prelude.Function
open import Prelude.Function.Fam
open import Prelude.InverseImage
open import Prelude.Category.Slice
open import Prelude.Category.Span
open import Prelude.Category.Pullback
open import Description
open import Description.Horizontal
open import Ornament
open import Ornament.SequentialComposition
open import Ornament.Equivalence
open import Ornament.Category
open import Ornament.Horizontal
open import Ornament.Horizontal.Category

open import Function using (_∘_)
open import Data.Product using (Σ; Σ-syntax; _,_; proj₁; proj₂)
open import Data.List using (List; []; _∷_; map)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; sym)
open import Relation.Binary.HeterogeneousEquality using (_≅_; ≡-to-≅) renaming (refl to hrefl; trans to htrans)

open Functor


coherence-reconstruction :
  {I : Set} (f g : Slice Fun I) (s : Square Fun f g) (ps : Pullback Fun f g s) (s' : Square Fun f g) (m : SquareMorphism Fun f g s' s) →
  let J  = Slice.T  f
      K  = Slice.T  g
      L  = Square-T s
      l  = SliceMorphism.m (Span.l s)
      r  = SliceMorphism.m (Span.r s)
      L' = Square-T s'
      l' = SliceMorphism.m (Span.l s')
      r' = SliceMorphism.m (Span.r s')
      f  = SquareMorphism-m m
  in  {xs' : List L'} {xs : List L} {ys : List J} {zs : List K} → Ė l xs ys → Ė r xs zs → Ė l' xs' ys → Ė r' xs' zs → Ė f xs' xs
coherence-reconstruction f g s ps s' m []        []         []         []         = []
coherence-reconstruction f g s ps s' m (_∷_ {l} q₀ es₀)(q₁ ∷ es₁) (_∷_ {l'} q₂ es₂) (q₃ ∷ es₃) =
  decouple' (Slice.s f) (Slice.s g) s ps (trans (SpanMorphism.triangle-l m l') (trans q₂ (sym q₀)))
                                         (trans (SpanMorphism.triangle-r m l') (trans q₃ (sym q₁)))
    ∷ coherence-reconstruction f g s ps s' m es₀ es₁ es₂ es₃

coherence-reconstruction' :
  {I : Set} (f g : Slice Fun I) (s : Square Fun f g) (ps : Pullback Fun f g s) (s' : Square Fun f g) (m : SquareMorphism Fun f g s' s) →
  let J  = Slice.T  f
      K  = Slice.T  g
      L  = Square-T s
      l  = SliceMorphism.m (Span.l s)
      r  = SliceMorphism.m (Span.r s)
      L' = Square-T s'
      l' = SliceMorphism.m (Span.l s')
      r' = SliceMorphism.m (Span.r s')
      f  = SquareMorphism-m m
  in  {xs' : List L'} {xs : List L} {ys ys' : List J} {zs zs' : List K} →
      Ė l xs ys → Ė r xs zs → Ė l' xs' ys' → Ė r' xs' zs' → ys ≡ ys' → zs ≡ zs' → Ė f xs' xs
coherence-reconstruction' f g s ps s' m es₀ es₁ es₂ es₃ refl refl = coherence-reconstruction f g s ps s' m es₀ es₁ es₂ es₃

next-lemma : {I : Set} {D D' : RDesc I} → D ≡ D' → {h : Ṡ D} {h' : Ṡ D'} → h ≅ h' → next D h ≡ next D' h'
next-lemma refl hrefl = refl

module ShapeReflectsPullback
  {I : Set} {D : Desc I} (f g : Slice ḞḢTrans (I , D)) (s : Square ḞḢTrans f g)
  (p : Pullback Fam (object (SliceMap Shape) f) (object (SliceMap Shape) g) (object (SquareMap Shape) s))
  (s' : Square ḞḢTrans f g) where

  L : Set
  L = proj₁ (Square-T s)

  G : Desc L
  G = proj₂ (Square-T s)

  L' : Set
  L' = proj₁ (Square-T s')

  G' : Desc L'
  G' = proj₂ (Square-T s')

  Fam-med : SquareMorphism Fam (object (SliceMap Shape) f) (object (SliceMap Shape) g)
              (object (SquareMap Shape) s') (object (SquareMap Shape) s)
  Fam-med = proj₁ (p (object (SquareMap Shape) s'))

  med : SquareMorphism ḞḢTrans f g s' s
  med = spanMorphism
          (sliceMorphism
             (FamMorphism.e (SquareMorphism-m Fam-med) ,
              wrap λ l → FamMorphism.u (SquareMorphism-m Fam-med) ,
                         λ h → coherence-reconstruction'
                                 (object (SliceMap (FamI ⋆ Shape)) f)
                                 (object (SliceMap (FamI ⋆ Shape)) g)
                                 (object (SquareMap (FamI ⋆ Shape)) s)
                                 (FamI-preserves-pullback (object (SliceMap Shape) f) (object (SliceMap Shape) g) (object (SquareMap Shape) s) p)
                                 (object (SquareMap (FamI ⋆ Shape)) s')
                                 (morphism (SquareMap FamI) Fam-med)
                                 (ḢTrans.c (FḢTrans.comp (proj₂ (SliceMorphism.m (Span.l s))) (FamMorphism.e (SquareMorphism-m Fam-med) l))
                                    (FamMorphism.u (SquareMorphism-m Fam-med) h))
                                 (ḢTrans.c (FḢTrans.comp (proj₂ (SliceMorphism.m (Span.r s))) (FamMorphism.e (SquareMorphism-m Fam-med) l))
                                    (FamMorphism.u (SquareMorphism-m Fam-med) h))
                                 (ḢTrans.c (FḢTrans.comp (proj₂ (SliceMorphism.m (Span.l s'))) l) h)
                                 (ḢTrans.c (FḢTrans.comp (proj₂ (SliceMorphism.m (Span.r s'))) l) h)
                                 (next-lemma (cong (Desc.comp (proj₂ (Slice.T f))) (FamMorphismEq.e (SpanMorphism.triangle-l Fam-med) l))
                                             (FamMorphismEq.u (SpanMorphism.triangle-l Fam-med) h h hrefl))
                                 (next-lemma (cong (Desc.comp (proj₂ (Slice.T g))) (FamMorphismEq.e (SpanMorphism.triangle-r Fam-med) l))
                                             (FamMorphismEq.u (SpanMorphism.triangle-r Fam-med) h h hrefl)))
             (FamMorphismEq.e (SliceMorphism.triangle (SpanMorphism.m Fam-med)) ,
              λ l h → FamMorphismEq.u (SliceMorphism.triangle (SpanMorphism.m Fam-med)) h h hrefl))
          (FamMorphismEq.e (SpanMorphism.triangle-l Fam-med) , λ l h → FamMorphismEq.u (SpanMorphism.triangle-l Fam-med) h h hrefl)
          (FamMorphismEq.e (SpanMorphism.triangle-r Fam-med) , λ l h → FamMorphismEq.u (SpanMorphism.triangle-r Fam-med) h h hrefl)

  module Uniqueness (med' : SquareMorphism ḞḢTrans f g s' s) where

    Fam-med-equals-med' : FamMorphismEq (Square-T (object (SquareMap Shape) s')) (Square-T (object (SquareMap Shape) s))
                            (SquareMorphism-m Fam-med) (SquareMorphism-m (morphism (SquareMap Shape) med'))
    Fam-med-equals-med' = proj₂ (p (object (SquareMap Shape) s')) (morphism (SquareMap Shape) med')

    index-unique : proj₁ (SquareMorphism-m med) ≐ proj₁ (SquareMorphism-m med')
    index-unique = FamMorphismEq.e Fam-med-equals-med'

    FḢTrans-unique : (l : L') (h : Ṡ (Desc.comp G' l)) → ḢTrans.s (FḢTrans.comp (proj₂ (SquareMorphism-m med )) l) h ≅
                                                         ḢTrans.s (FḢTrans.comp (proj₂ (SquareMorphism-m med')) l) h
    FḢTrans-unique l h = FamMorphismEq.u Fam-med-equals-med' h h hrefl

Shape-reflects-pullback : Pullback-reflecting Shape
Shape-reflects-pullback f g s p s' =
  ShapeReflectsPullback.med f g s p s' ,
  λ med' → ShapeReflectsPullback.Uniqueness.index-unique f g s p s' med' , ShapeReflectsPullback.Uniqueness.FḢTrans-unique f g s p s' med'

Erase-reflects-pullback : Pullback-reflecting Erase
Erase-reflects-pullback f g s ps s' =
  let m = proj₁ (ps (object (SquareMap Erase) s'))
  in  spanMorphism (sliceMorphism (proj₁ (SquareMorphism-m m) , wrap λ { {._} (ok l) → ḢROrn (FḢTrans.comp (proj₂ (SquareMorphism-m m)) l) })
                                  (proj₁ (SliceMorphism.triangle (SpanMorphism.m m)) ,
                                   λ j hs → htrans (≡-to-≅ (erase-Ṡ-scROrn (Orn.comp (proj₂ (Slice.s (Span.M s))) (ok (proj₁ (SquareMorphism-m m) j)))
                                                                           (ḢROrn (FḢTrans.comp (proj₂ (SquareMorphism-m m)) j)) hs))
                                                   (htrans (≡-to-≅ (cong (erase-Ṡ (Orn.comp (proj₂ (Slice.s (Span.M s))) (ok (proj₁ (SquareMorphism-m m) j))))
                                                                         (erase-Ṡ-ḢROrn (FḢTrans.comp (proj₂ (SquareMorphism-m m)) j) hs)))
                                                           (proj₂ (SliceMorphism.triangle (SpanMorphism.m m)) j hs))))
                   (proj₁ (SpanMorphism.triangle-l m) ,
                    λ j hs → htrans (≡-to-≅ (erase-Ṡ-scROrn (Orn.comp (proj₂ (SliceMorphism.m (Span.l s))) (ok (proj₁ (SquareMorphism-m m) j)))
                                                            (ḢROrn (FḢTrans.comp (proj₂ (SquareMorphism-m m)) j)) hs))
                                    (htrans (≡-to-≅ (cong (erase-Ṡ (Orn.comp (proj₂ (SliceMorphism.m (Span.l s))) (ok (proj₁ (SquareMorphism-m m) j))))
                                                          (erase-Ṡ-ḢROrn (FḢTrans.comp (proj₂ (SquareMorphism-m m)) j) hs)))
                                            (proj₂ (SpanMorphism.triangle-l m) j hs)))
                   (proj₁ (SpanMorphism.triangle-r m) ,
                    λ j hs → htrans (≡-to-≅ (erase-Ṡ-scROrn (Orn.comp (proj₂ (SliceMorphism.m (Span.r s))) (ok (proj₁ (SquareMorphism-m m) j)))
                                                            (ḢROrn (FḢTrans.comp (proj₂ (SquareMorphism-m m)) j)) hs))
                                    (htrans (≡-to-≅ (cong (erase-Ṡ (Orn.comp (proj₂ (SliceMorphism.m (Span.r s))) (ok (proj₁ (SquareMorphism-m m) j))))
                                                          (erase-Ṡ-ḢROrn (FḢTrans.comp (proj₂ (SquareMorphism-m m)) j) hs)))
                                            (proj₂ (SpanMorphism.triangle-r m) j hs))) ,
      λ m' → let meq = proj₂ (ps (object (SquareMap Erase) s')) (morphism (SquareMap Erase) m')
             in  proj₁ meq , λ j hs → htrans (≡-to-≅ (erase-Ṡ-ḢROrn (FḢTrans.comp (proj₂ (SquareMorphism-m m)) j) hs)) (proj₂ meq j hs)
