open import Thesis.Prelude.Category
open import Thesis.Prelude.Category.Isomorphism
open import Thesis.Prelude.Function.Fam
open import Thesis.Ornament
open import Thesis.Ornament.Category

open import Data.Product using (Σ; _,_; proj₁; proj₂)

open Functor

module Thesis.Ornament.SequentialComposition.Swap
  {I J K : Set} {e : J → I} {f : K → J} {D E F} (O : Orn e D E) (P : Orn f E F) (piso : PartOfIso Fam (morphism Ind (f , P))) where

open import Thesis.Prelude.Equality
open import Thesis.Prelude.Function
open import Thesis.Prelude.Category.Slice
open import Thesis.Prelude.Category.Span
open import Thesis.Prelude.Category.Pullback
open import Thesis.Prelude.InverseImage
open import Thesis.Refinement
open import Thesis.Description
open import Thesis.Ornament.SequentialComposition
open import Thesis.Ornament.ParallelComposition
open import Thesis.Ornament.ParallelComposition.Pullback
open import Thesis.Ornament.RefinementSemantics

open import Relation.Binary using (module Setoid)
import Relation.Binary.EqReasoning as EqReasoning
open import Relation.Binary.PropositionalEquality using (_≡_; refl)


private

  open Category Fam

  p' : Span (SliceCategory Fam (object Ind (_ , D))) (slice _ (morphism Ind (_ , O ⊙ P))) (slice _ (morphism Ind (_ , ⌈ singOrn D ⌉)))
  p' = proj₁ (proj₁ (⊗-is-Pullback (O ⊙ P) ⌈ singOrn D ⌉))

  p : Span (SliceCategory Fam (object Ind (_ , D))) (slice _ (morphism Ind (_ , O))) (slice _ (morphism Ind (_ , ⌈ singOrn D ⌉)))
  p = span (Span.M p')
           (sliceMorphism
             (morphism Ind (_ , P ⊙ diffOrn-l (O ⊙ P) ⌈ singOrn D ⌉))
             (begin
                morphism Ind (_ , O) · morphism Ind (_ , P ⊙ diffOrn-l (O ⊙ P) ⌈ singOrn D ⌉)
                  ≈⟨ cong-l (morphism Ind (_ , O)) (comp-preserving Ind (_ , P) (_ , diffOrn-l (O ⊙ P) ⌈ singOrn D ⌉)) ⟩
                morphism Ind (_ , O) · morphism Ind (_ , P) · morphism Ind (_ , diffOrn-l (O ⊙ P) ⌈ singOrn D ⌉)
                  ≈⟨ sym (cong-r (morphism Ind (_ , diffOrn-l (O ⊙ P) ⌈ singOrn D ⌉)) (comp-preserving Ind (_ , O) (_ , P))) ⟩
                morphism Ind (_ , O ⊙ P) · morphism Ind (_ , diffOrn-l (O ⊙ P) ⌈ singOrn D ⌉)
                  ≈⟨ SliceMorphism.triangle (Span.l p') ⟩
                morphism Ind (_ , ⌈ (O ⊙ P) ⊗ ⌈ singOrn D ⌉ ⌉)
              □))
           (Span.r p')
    where setoid = Morphism (object Ind (_ , ⌊ (O ⊙ P) ⊗ ⌈ singOrn D ⌉ ⌋)) (object Ind (_ , D))
          open Setoid setoid
          open EqReasoning setoid renaming (_∎ to _□)

  module Universality
    (q : Span (SliceCategory Fam (object Ind (_ , D))) (slice _ (morphism Ind (_ , O))) (slice _ (morphism Ind (_ , ⌈ singOrn D ⌉)))) where

    q' : Span (SliceCategory Fam (object Ind (_ , D))) (slice _ (morphism Ind (_ , O ⊙ P))) (slice _ (morphism Ind (_ , ⌈ singOrn D ⌉)))
    q' = span (Span.M q)
              (sliceMorphism
                (PartOfIso.from Fam piso · SliceMorphism.m (Span.l q))
                (begin
                   morphism Ind (_ , O ⊙ P) · PartOfIso.from Fam piso · SliceMorphism.m (Span.l q)
                     ≈⟨ cong-r (PartOfIso.from Fam piso · SliceMorphism.m (Span.l q)) (comp-preserving Ind (_ , O) (_ , P)) ⟩
                   morphism Ind (_ , O) · morphism Ind (_ , P) · PartOfIso.from Fam piso · SliceMorphism.m (Span.l q)
                     ≈⟨ cong-l (morphism Ind (_ , O)) (cong-r (SliceMorphism.m (Span.l q)) (PartOfIso.to-from-inverse Fam piso)) ⟩
                   morphism Ind (_ , O) · SliceMorphism.m (Span.l q)
                     ≈⟨ SliceMorphism.triangle (Span.l q) ⟩
                   Slice.s (Span.M q)
                 □))
              (Span.r q)
      where setoid = Morphism (Slice.T (Span.M q)) (object Ind (_ , D))
            open Setoid setoid
            open EqReasoning setoid renaming (_∎ to _□)

    med' : SpanMorphism (SliceCategory Fam (object Ind (_ , D)))
                        (slice _ (morphism Ind (_ , O ⊙ P))) (slice _ (morphism Ind (_ , ⌈ singOrn D ⌉))) q' p'
    med' = proj₁ (proj₂ (⊗-is-Pullback (O ⊙ P) ⌈ singOrn D ⌉) q')

    med : SpanMorphism (SliceCategory Fam (object Ind (_ , D))) (slice _ (morphism Ind (_ , O))) (slice _ (morphism Ind (_ , ⌈ singOrn D ⌉))) q p
    med = spanMorphism
            (SpanMorphism.m med')
            (begin
               morphism Ind (_ , P ⊙ diffOrn-l (O ⊙ P) ⌈ singOrn D ⌉) · SliceMorphism.m (SpanMorphism.m med')
                 ≈⟨ cong-r (SliceMorphism.m (SpanMorphism.m med')) (comp-preserving Ind (_ , P) (_ , diffOrn-l (O ⊙ P) ⌈ singOrn D ⌉)) ⟩
               morphism Ind (_ , P) · morphism Ind (_ , diffOrn-l (O ⊙ P) ⌈ singOrn D ⌉) · SliceMorphism.m (SpanMorphism.m med')
                 ≈⟨ cong-l (morphism Ind (_ , P)) (SpanMorphism.triangle-l med') ⟩
               morphism Ind (_ , P) · PartOfIso.from Fam piso · SliceMorphism.m (Span.l q)
                 ≈⟨ cong-r (SliceMorphism.m (Span.l q)) (PartOfIso.to-from-inverse Fam piso) ⟩
               SliceMorphism.m (Span.l q)
             □)
            (SpanMorphism.triangle-r med')
      where setoid = Morphism (Slice.T (Span.M q)) (object Ind (_ , E))
            open EqReasoning setoid renaming (_∎ to _□)

    uniqueness :
      Unique (Category.Morphism
               (SpanCategory (SliceCategory Fam (object Ind (_ , D))) (slice _ (morphism Ind (_ , O)))
                                                                      (slice _ (morphism Ind (_ , ⌈ singOrn D ⌉))))
               q p)
        med
    uniqueness med'' =
      proj₂ (proj₂ (⊗-is-Pullback (O ⊙ P) ⌈ singOrn D ⌉) q')
        (spanMorphism
           (SpanMorphism.m med'')
           (begin
              morphism Ind (_ , diffOrn-l (O ⊙ P) ⌈ singOrn D ⌉) · SliceMorphism.m (SpanMorphism.m med'')
                ≈⟨ Setoid.sym setoid
                     (cong-r (morphism Ind (_ , diffOrn-l (O ⊙ P) ⌈ singOrn D ⌉) · SliceMorphism.m (SpanMorphism.m med''))
                             (PartOfIso.from-to-inverse Fam piso)) ⟩
              PartOfIso.from Fam piso · morphism Ind (_ , P) ·
                morphism Ind (_ , diffOrn-l (O ⊙ P) ⌈ singOrn D ⌉) · SliceMorphism.m (SpanMorphism.m med'')
                ≈⟨ Setoid.sym setoid
                     (cong-l (PartOfIso.from Fam piso) (cong-r (SliceMorphism.m (SpanMorphism.m med''))
                             (comp-preserving Ind (_ , P) (_ , diffOrn-l (O ⊙ P) ⌈ singOrn D ⌉)))) ⟩
              PartOfIso.from Fam piso · morphism Ind (_ , P ⊙ diffOrn-l (O ⊙ P) ⌈ singOrn D ⌉) · SliceMorphism.m (SpanMorphism.m med'')
                ≈⟨ cong-l (PartOfIso.from Fam piso) (SpanMorphism.triangle-l med'') ⟩
              PartOfIso.from Fam piso · SliceMorphism.m (Span.l q)
            □)
           (SpanMorphism.triangle-r med''))
      where setoid = Morphism (Slice.T (Span.M q)) (object Ind (_ , F))
            open EqReasoning setoid renaming (_∎ to _□)

  p-pullback : Pullback Fam (slice _ (morphism Ind (_ , O))) (slice _ (morphism Ind (_ , ⌈ singOrn D ⌉)))
                            (object Ind (_ , ⌊ (O ⊙ P) ⊗ ⌈ singOrn D ⌉ ⌋))
  p-pullback = (p , refl) , λ q → Universality.med q , Universality.uniqueness q

  isos : ∀ {k} (x : μ D (e (f k))) → Iso Fun (OptP (O ⊙ P) (ok k) x) (OptP O (ok (f k)) x)
  isos {k} x =
    compIso (pullback-iso Fam (slice _ (morphism Ind (_ , O))) (slice _ (morphism Ind (_ , ⌈ singOrn D ⌉)))
                              (object Ind (_ , ⌊ (O ⊙ P) ⊗ ⌈ singOrn D ⌉ ⌋)) (object Ind (_ , ⌊ O ⊗ ⌈ singOrn D ⌉ ⌋))
                              p-pullback (⊗-is-Pullback O ⌈ singOrn D ⌉))
            (ok k , ok (e (f k) , x))

⊙-FSwap : FSwap (RSem' O) → FSwap (RSem' (O ⊙ P))
⊙-FSwap s =
  wrap λ { {._} (ok k) →
           record { Q = Swap.Q (FSwap.comp s (ok (f k)))
                  ; s = λ x → Setoid.trans (IsoSetoid Fun) (isos x) (Swap.s (FSwap.comp s (ok (f k))) x) } }
