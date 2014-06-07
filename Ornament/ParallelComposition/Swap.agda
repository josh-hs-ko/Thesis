-- The optimised predicate for the parallel composition of two ornaments can be swapped
-- for the pointwise conjunction of the optimised predicates for the two component ornaments.
-- This file can take a long time to typecheck and may require a larger stack size.

open import Ornament

module Ornament.ParallelComposition.Swap {I J K} {e : J → I} {f : K → I} {D E F} (O : Orn e D E) (P : Orn f D F) where

open import Prelude.Equality
open import Prelude.Function
open import Prelude.Function.Fam
open import Prelude.Function.Isomorphism hiding (compIso)
open import Prelude.Product
open import Prelude.Category
open import Prelude.Category.Isomorphism
open import Prelude.Category.Slice
open import Prelude.Category.Slice.Functor
open import Prelude.Category.Span
open import Prelude.Category.Pullback
open import Prelude.Category.Pullback.Midpoint
open import Prelude.InverseImage
open import Refinement
open import Description
open import Ornament.Category
open import Ornament.ParallelComposition
open import Ornament.ParallelComposition.Pullback
open import Ornament.RefinementSemantics

open import Function using (id; _∘_)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_; <_,_>; uncurry) renaming (map to _**_)
open import Relation.Binary using (module Setoid)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; cong; cong₂) renaming (setoid to ≡-Setoid)
open import Relation.Binary.HeterogeneousEquality using (_≅_; ≡-to-≅) renaming (proof-irrelevance to hproof-irrelevance)

open Functor


private

  l : Slice Fam (object Ind (Σ I (μ D) , ⌊ singOrn D ⌋))
  l = object (SliceMap Ind) (slice _ (_ , diffOrn-r O ⌈ singOrn D ⌉))

  r : Slice Fam (object Ind (Σ I (μ D) , ⌊ singOrn D ⌋))
  r = object (SliceMap Ind) (slice _ (_ , diffOrn-r P ⌈ singOrn D ⌉))

  O⊗P-square : Square Fam (object (SliceMap Ind) (Ōrn-slice O)) (object (SliceMap Ind) (Ōrn-slice P))
  O⊗P-square = ⊗-Fam-square O P

  O⊗P-terminal : Pullback Fam (object (SliceMap Ind) (Ōrn-slice O)) (object (SliceMap Ind) (Ōrn-slice P)) O⊗P-square
  O⊗P-terminal = ⊗-is-Fam-pullback O P

  OptP-O-square : Square Fam (object (SliceMap Ind) (Ōrn-slice O)) (object (SliceMap Ind) (Ōrn-slice ⌈ singOrn D ⌉))
  OptP-O-square = ⊗-Fam-square O ⌈ singOrn D ⌉

  OptP-O-terminal : Pullback Fam (object (SliceMap Ind) (Ōrn-slice O)) (object (SliceMap Ind) (Ōrn-slice ⌈ singOrn D ⌉)) OptP-O-square
  OptP-O-terminal = ⊗-is-Fam-pullback O ⌈ singOrn D ⌉

  OptP-P-square : Square Fam (object (SliceMap Ind) (Ōrn-slice P)) (object (SliceMap Ind) (Ōrn-slice ⌈ singOrn D ⌉))
  OptP-P-square = ⊗-Fam-square P ⌈ singOrn D ⌉

  OptP-P-terminal : Pullback Fam (object (SliceMap Ind) (Ōrn-slice P)) (object (SliceMap Ind) (Ōrn-slice ⌈ singOrn D ⌉)) OptP-P-square
  OptP-P-terminal = ⊗-is-Fam-pullback P ⌈ singOrn D ⌉

  OptP-O⊗P-square : Square Fam (object (SliceMap Ind) (Ōrn-slice ⌈ O ⊗ P ⌉)) (object (SliceMap Ind) (Ōrn-slice ⌈ singOrn D ⌉))
  OptP-O⊗P-square = ⊗-Fam-square ⌈ O ⊗ P ⌉ ⌈ singOrn D ⌉

  OptP-O⊗P-terminal : Pullback Fam (object (SliceMap Ind) (Ōrn-slice ⌈ O ⊗ P ⌉)) (object (SliceMap Ind) (Ōrn-slice ⌈ singOrn D ⌉)) OptP-O⊗P-square
  OptP-O⊗P-terminal = ⊗-is-Fam-pullback ⌈ O ⊗ P ⌉ ⌈ singOrn D ⌉

  mp-square : Square Fam l r
  mp-square = object (SpanMap (SliceMap SliceU))
                (midpoint-square (SliceCategory Fam (object Ind (I , D)))
                                 (object (SliceMap Ind) (slice _ (_ , O)))
                                 (object (SliceMap Ind) (slice _ (_ , P)))
                                 (object (SliceMap Ind) (slice _ (_ , ⌈ singOrn D ⌉)))
                                 O⊗P-square      O⊗P-terminal
                                 OptP-O-square   OptP-O-terminal
                                 OptP-P-square   OptP-P-terminal
                                 OptP-O⊗P-square OptP-O⊗P-terminal)

  p : Pullback Fam l r mp-square
  p = SliceU-preserves-pullback (object SpanUR OptP-O-square) (object SpanUR OptP-P-square) _
        (midpoint-pullback (SliceCategory Fam (object Ind (I , D)))
                                              (object (SliceMap Ind) (slice _ (_ , O)))
                                              (object (SliceMap Ind) (slice _ (_ , P)))
                                              (object (SliceMap Ind) (slice _ (_ , ⌈ singOrn D ⌉)))
                                              O⊗P-square      O⊗P-terminal
                                              OptP-O-square   OptP-O-terminal
                                              OptP-P-square   OptP-P-terminal
                                              OptP-O⊗P-square OptP-O⊗P-terminal)

  l' : pull {J} {K} {I} {e} {f} ⋈ proj₁ {A = I} {μ D} → e ⋈ proj₁ {A = I} {μ D}
  l' = SliceMorphism.m
         (SpanMorphism.m
          (proj₁ (⋈-is-pullback e (proj₁ {A = I} {μ D})
            (let X×Y×Z = ⋈-square (pull {J} {K} {I} {e} {f}) (proj₁ {A = I} {μ D})
                 X×Y   = ⋈-square e f
             in span (Span.M X×Y×Z) (Category._·_ (SliceCategory Fun I) (Span.l X×Y) (Span.l X×Y×Z)) (Span.r X×Y×Z)))))

  r' : pull {J} {K} {I} {e} {f} ⋈ proj₁ {A = I} {μ D} → f ⋈ proj₁ {A = I} {μ D}
  r' = SliceMorphism.m
         (SpanMorphism.m
          (proj₁ (⋈-is-pullback f (proj₁ {A = I} {μ D})
            (let X×Y×Z = ⋈-square (pull {J} {K} {I} {e} {f}) (proj₁ {A = I} {μ D})
                 X×Y   = ⋈-square e f
             in span (Span.M X×Y×Z) (Category._·_ (SliceCategory Fun I) (Span.r X×Y) (Span.l X×Y×Z)) (Span.r X×Y×Z)))))

  wholeIso : Iso Fam (object Ind (_ , OptPD ⌈ O ⊗ P ⌉)) (Square-T (Mix-square l r))
  wholeIso = pullback-iso Fam l r mp-square (Mix-square l r) p (canonPullback l r)

  canonIso-l : {i : I} (j : e ⁻¹ i) (k : f ⁻¹ i) (x : μ D i) → Iso Fun (μ (OptPD O) (l' (ok (j , k) , ok (i , x)))) (OptP O j x)
  canonIso-l (ok j) k x = Setoid.refl (IsoSetoid Fun)

  canonIso-r : {i : I} (j : e ⁻¹ i) (k : f ⁻¹ i) (x : μ D i) → Iso Fun (μ (OptPD P) (r' (ok (j , k) , ok (i , x)))) (OptP P k x)
  canonIso-r j (ok k) x = Setoid.refl (IsoSetoid Fun)

  canonIso : {i : I} {j : e ⁻¹ i} {k : f ⁻¹ i} (x : μ D i) →
             Iso Fun (Σ (μ (OptPD O) (l' (ok (j , k) , ok (i , x))) × μ (OptPD P) (r' (ok (j , k) , ok (i , x))))
                      λ { (y , z) → forget (diffOrn-r O ⌈ singOrn D ⌉) y ≅ forget (diffOrn-r P ⌈ singOrn D ⌉) z})
                     (OptP O j x × OptP P k x)
  canonIso {i} {j} {k} x = Setoid.trans (IsoSetoid Fun)
                             (record { to   = proj₁
                                     ; from = λ yz → yz , ≡-to-≅ (equal (≡-Setoid _) (singleton x , singleton-unique x) _ _)
                                     ; to-from-inverse = frefl
                                     ; from-to-inverse = λ { ((y Data.Product., z) , eq) →
                                                             cong₂-pair refl (≡-to-≅ (hproof-irrelevance _ _)) } })
                             (prodIso (canonIso-l j k x) (canonIso-r j k x))

  splittingIso : {i : I} {j : e ⁻¹ i} {k : f ⁻¹ i} (x : μ D i) → Iso Fun (OptP ⌈ O ⊗ P ⌉ (ok (j , k)) x) (OptP O j x × OptP P k x)
  splittingIso {i} {j} {k} x = Setoid.trans (IsoSetoid Fun) (compIso wholeIso (ok (j , k) , ok (i , x))) (canonIso x)


--------
-- predicate swap

⊗-FSwap : FSwap (RSem' O) → FSwap (RSem' P) → FSwap (RSem' ⌈ O ⊗ P ⌉)
⊗-FSwap (wrap s) (wrap t) =
  wrap λ { {._} (ok (j , k)) →
           record { Q = λ x → Swap.Q (s j) x × Swap.Q (t k) x
                  ; s = λ x → Setoid.trans (IsoSetoid Fun) (splittingIso x) (prodIso (Swap.s (s j) x) (Swap.s (t k) x)) } }
