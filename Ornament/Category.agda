-- The category of descriptions and ornaments.
-- The functor `Ind` (for "induction") takes the least fixed points of descriptions and
-- extends ornaments to forgetful maps on those least fixed points.

module Ornament.Category where

open import Prelude.Category
open import Prelude.Function
open import Prelude.Function.Fam
open import Prelude.Product
open import Prelude.InverseImage
open import Refinement
open import Refinement.Category
open import Description
open import Ornament
open import Ornament.Equivalence
open import Ornament.SequentialComposition

open import Function using (id; _∘_)
open import Data.Product using (Σ; Σ-syntax; proj₁; _,_) renaming (map to _**_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; module ≡-Reasoning)
open import Relation.Binary.HeterogeneousEquality using (_≅_; ≡-to-≅) renaming (refl to hrefl)


Ōrn : Category
Ōrn =  record { Object   = Σ Set Desc
              ; Morphism = λ { (J , E) (I , D) → 
                               record { Carrier = Σ[ e ∈ (J → I) ] Orn e D E
                                      ; _≈_ = λ { (e , O) (f , P) → OrnEq O P }
                                      ; isEquivalence =
                                          record { refl  = λ { {e , O} → OrnEq-refl O }
                                                 ; sym   = λ { {e , O} {f , P} → OrnEq-sym O P }
                                                 ; trans = λ { {e , O} {f , P} {g , Q} → OrnEq-trans O P Q } } } }
              ; _·_ = λ { (e , O) (f , P) → e ∘ f , O ⊙ P }
              ; id  = λ { {I , D} → id , idOrn D }
              ; id-l   = λ { (e , O) → ⊙-id-l O }
              ; id-r   = λ { (e , O) → ⊙-id-r O }
              ; assoc  = λ { (e , O) (f , P) (g , Q) → ⊙-assoc O P Q }
              ; cong-l = λ { {_} {_} {_} {e , O} {f , P} (g , Q) eq → ⊙-cong-l Q O P eq }
              ; cong-r = λ { {_} {_} {_} {e , O} {f , P} (g , Q) eq → ⊙-cong-r Q O P eq } }

Ind : Functor Ōrn Fam
Ind = record { object   = λ { (I , D) → I , μ D }
             ; morphism = λ { (e , O) → e , forget O }
             ; ≈-respecting    = λ { {_} {_} {e , O} {f , P} (eeq , oeq) → eeq , (λ { x .x hrefl → OrnEq-forget O P (eeq , oeq) x}) }
             ; id-preserving   = frefl , (λ { x .x hrefl → ≡-to-≅ (forget-idOrn x) })
             ; comp-preserving = λ { (e , O) (f , P) → frefl , (λ { x .x hrefl → ≡-to-≅ (forget-after-forget O P x) }) } }
