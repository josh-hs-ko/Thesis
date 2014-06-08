-- Families of refinements form a category `FRef`.

module Refinement.Category where

open import Prelude.Category
open import Prelude.Function
open import Prelude.Function.Fam
open import Prelude.InverseImage
open import Prelude.Product
open import Refinement

open import Function using (_∘_)
open import Data.Product using (Σ; Σ-syntax; _,_; proj₁; proj₂; _×_; <_,_>)
open import Relation.Binary using (module Setoid)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; cong)
open import Relation.Binary.HeterogeneousEquality using (_≅_) renaming (refl to hrefl)

FRef : Category
FRef = record { Object   = Σ[ I ∈ Set ] (I → Set)
              ; Morphism = λ { (J , Y) (I , X) →
                                 record { Carrier = Σ[ e ∈ (J → I) ] FRefinement e X Y
                                        ; _≈_ = λ { (e , r) (f , s) →
                                                    FamMorphismEq (J , Y) (I , X) (e , FRefinement.forget r) (f , FRefinement.forget s) }
                                        ; isEquivalence =
                                            record { refl = frefl , ≑-refl
                                                   ; sym = λ { (eeq , req) → fsym eeq , ≑-sym req }
                                                   ; trans = λ { (eeq , req) (eeq' , req') → ftrans eeq eeq' , ≑-trans refl req req'} } } }
              ; _·_ = λ { (e , r) (f , s) → (e ∘ f) , FRef-trans r s }
              ; id  = Function.id , FRef-refl
              ; id-l   = λ { (e , r) → frefl , ≑-refl }
              ; id-r   = λ { (e , r) → frefl , ≑-refl }
              ; assoc  = λ _ _ _ → frefl , ≑-refl
              ; cong-l = λ { {I , X} {J , Y} {K , Z} {e , r} {f , s} (g , t) (eeq , req) →
                              fcong-l g eeq ,
                              λ {i} → ≑-cong-l (FRefinement.forget t) (FRefinement.forget t)
                                               (subst (λ j → (x : Y (e i)) (x' : Y j) →
                                                             x ≅ x' → FRefinement.forget t x ≅ FRefinement.forget t x')
                                                      (eeq i) ≑-refl)
                                               req }
              ; cong-r = λ { {I , X} {J , Y} {K , Z} {e , r} {f , s} (g , t) (eeq , req) →
                              fcong-r g eeq , λ {i} → ≑-cong-r (FRefinement.forget t) (FRefinement.forget t) ≑-refl req } }

FRefF : Functor FRef Fam
FRefF = record { object   = Function.id
               ; morphism = λ { (e , r) → e , FRefinement.forget r }
               ; ≈-respecting    = λ { (eq , eq') → eq , eq' }
               ; id-preserving   = frefl , ≑-refl
               ; comp-preserving = λ _ _ → frefl , ≑-refl }

FRefC : Functor Fam FRef
FRefC = record { object   = Function.id
               ; morphism = λ { {J , Y} {I , X} (e , u) → e , canonFRef u }
               ; ≈-respecting    = λ { (eq , eq') → eq , eq' }
               ; id-preserving   = frefl , ≑-refl
               ; comp-preserving = λ _ _ → frefl , ≑-refl }
