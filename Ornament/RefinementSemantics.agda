-- Definition of an optimised predicate for an ornament as the parallel composition of the ornament and the singleton ornament.
-- This construction gives a functor from `Orn` to `FRef` which produces more representation-efficient promotion predicates.

module Ornament.RefinementSemantics where

open import Prelude.Equality
open import Prelude.Category
open import Prelude.Category.Isomorphism
open import Prelude.Category.Slice
open import Prelude.Category.Span
open import Prelude.Category.Pullback
open import Prelude.Function
open import Prelude.Function.Fam hiding (compIso)
open import Prelude.Function.Isomorphism
open import Prelude.Product
open import Prelude.InverseImage
open import Refinement
open import Refinement.Category
open import Description
open import Description.HorizontalEquivalence
open import Ornament
open import Ornament.Category
open import Ornament.Equivalence
open import Ornament.SequentialComposition
open import Ornament.ParallelComposition
open import Ornament.ParallelComposition.Pullback

open import Function using (id; _∘_)
open import Data.Product using (Σ; proj₁; proj₂; _,_; _×_; <_,_>) renaming (map to _**_)
open import Relation.Binary using (module Setoid)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; cong; trans; sym; module ≡-Reasoning) renaming (setoid to ≡-Setoid)
open import Relation.Binary.HeterogeneousEquality using (_≅_; ≡-to-≅; ≡-subst-removable) renaming (refl to hrefl; cong to hcong; trans to htrans)

open Functor

module OptimisedPredicate {I J} {e : J → I} {D E} (O : Orn e D E) where

  OptPD : Desc (e ⋈ proj₁)
  OptPD = ⌊ O ⊗ ⌈ singOrn D ⌉ ⌋

  OptPO : Orn π₁ E OptPD
  OptPO = diffOrn-l O ⌈ singOrn D ⌉

  OptP : ∀ {i} → e ⁻¹ i → μ D i → Set
  OptP j x = μ OptPD (j , (ok (_ , x)))

  l : Slice Fun (Σ I (μ D))
  l = object (SliceMap (FamF ⋆ Ind)) (slice _ (_ , O))

  r : Slice Fun (Σ I (μ D))
  r = object (SliceMap (FamF ⋆ Ind)) (slice _ (_ , ⌈ singOrn D ⌉))

  μE-span : Span (SliceCategory Fun (Σ I (μ D))) l r
  μE-span = span l (sliceMorphism id frefl)
                   (sliceMorphism < e ** forget O , singleton ∘ forget O ∘ proj₂ >
                                  (λ { (j , y) → cong₂-pair refl (≡-to-≅ (forget-singOrn (singleton (forget O y)))) }))

  μE-med : (p : Span (SliceCategory Fun (Σ I (μ D))) l r) → SpanMorphism (SliceCategory Fun (Σ I (μ D))) l r p μE-span
  μE-med p = spanMorphism (Span.l p) frefl
               (λ t → let eq  = trans (SliceMorphism.triangle (Span.l p) t) (sym (SliceMorphism.triangle (Span.r p) t))
                          eq' = cong₂-pair (cong proj₁ eq)
                                  (htrans (hcong proj₂ (≡-to-≅ eq))
                                          (≡-to-≅ (forget-singOrn (proj₂ (SliceMorphism.m (Span.r p) t)))))
                      in cong₂-pair eq'
                                   (htrans (≡-to-≅ (equal (≡-Setoid _) (singleton _ , singleton-unique _) _ _))
                                           (≡-subst-removable (μ ⌊ singOrn D ⌋) (sym eq') (proj₂ (SliceMorphism.m (Span.r p) t)))))

  μE-med-unique : (p : Span (SliceCategory Fun (Σ I (μ D))) l r) →
                  Unique (Category.Morphism (SpanCategory (SliceCategory Fun (Σ I (μ D))) l r) p μE-span) (μE-med p)
  μE-med-unique p med' = fsym (SpanMorphism.triangle-l med')

  μE-pullback : Pullback Fun l r (Σ J (μ E))
  μE-pullback = (μE-span , refl) , (λ p → μE-med p , μE-med-unique p)

  OptP-pullback : Pullback Fun l r (Σ (e ⋈ proj₁) (μ OptPD))
  OptP-pullback = let p = ⊗-is-Pullback O ⌈ singOrn D ⌉
                  in  (object (SpanMap (SliceMap FamF)) (proj₁ (proj₁ p)) , refl) ,
                      FamF-preserves-pullback (object (SliceMap Ind) (slice _ (_ , O)))
                                              (object (SliceMap Ind) (slice _ (_ , ⌈ singOrn D ⌉))) _ p

  wholeIso : Iso Fun (Σ (e ⋈ proj₁) (μ OptPD)) (Σ J (μ E))
  wholeIso = pullback-iso Fun l r (Σ (e ⋈ proj₁) (μ OptPD)) (Σ J (μ E)) OptP-pullback μE-pullback

  indexIso : ∀ j → Iso Fun (μ D (e j)) (Σ[ jix ∶ e ⋈ proj₁ {A = I} {μ D} ] π₁ jix ≡ j)
  indexIso j =
    record { to   = λ x → (ok j , ok (e j , x)) , refl
           ; from = λ { ((ok .j , ix) , refl) → subst (μ D) (to≡ ix) (proj₂ (und ix)) }
           ; to-from-inverse =
               λ { ((ok .j , ix) , refl) →
                   cong (λ ix' → (ok j , ix') , refl)
                     (elim-⁻¹ (λ {i} ix' → ok (i , subst (μ D) (to≡ ix') (proj₂ (und ix'))) ≡ ix') (λ ix' → refl) ix) }
           ; from-to-inverse = frefl }


  componentIso : ∀ {i} (j : e ⁻¹ i) → Iso Fun (μ E (und j)) (Σ (μ D i) (OptP j))
  componentIso (ok j) =
    Setoid.sym (IsoSetoid Fun)
      (compIso wholeIso π₁ (forget (diffOrn-l O ⌈ singOrn D ⌉)) frefl
               (μ D ∘ e) (λ {j'} → indexIso j') (forget O)
               (λ {j'} y →
                  decouple (cong proj₁ (SpanMorphism.triangle-l (proj₁ (proj₂ OptP-pullback (proj₁ (proj₁ μE-pullback)))) (j' , y))) refl)
               j)

open OptimisedPredicate public using (OptPD; OptPO; OptP)

OptPRD : ∀ {I J} {e : J → I} {D E} → ROrn e D E → ∀ {X} → ⟦ D ⟧ X → RDesc (e ⋈ proj₁)
OptPRD {D = D} O xs = toRDesc (pcROrn O (toROrn (erode D xs)))

RSem' : ∀ {I J} {e : J → I} {D E} (O : Orn e D E) → FRefinement e (μ D) (μ E)
RSem' O = wrap λ j → record { P = OptP O j
                            ; i = OptimisedPredicate.componentIso O j }

RSem : Functor Ōrn FRef
RSem = record { object   = λ { (I , D) → I , μ D }
              ; morphism = λ { {J , E} {I , D} (e , O) → e , RSem' O }
              ; ≈-respecting    = λ {X} {Y} {f} {g} → ≈-respecting Ind {X} {Y} {f} {g}
              ; id-preserving   = id-preserving Ind
              ; comp-preserving = comp-preserving Ind }
