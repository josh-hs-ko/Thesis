-- The category of descriptions and families of horizontal transformations, and
-- the equivalence between this category and the category `Ōrn` of descriptions and ornaments.

module Ornament.Horizontal.Category where

open import Prelude.Function
open import Prelude.Function.Fam
open import Prelude.InverseImage
open import Prelude.Category
open import Prelude.Category.Isomorphism
open import Prelude.Category.WCat
open import Description
open import Description.Horizontal
open import Ornament
open import Ornament.Equivalence
open import Ornament.SequentialComposition
open import Ornament.Horizontal
open import Ornament.Horizontal.Equivalence
open import Ornament.Category

open import Function using (id; const; _∘_)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; Σ-syntax; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; subst; cong)
open import Relation.Binary.HeterogeneousEquality using (_≅_; ≡-to-≅) renaming (refl to hrefl; sym to hsym; trans to htrans)


record FḢTrans {I J : Set} (e : J → I) (D : Desc I) (E : Desc J) : Set₁ where
  constructor wrap
  field
    comp : (j : J) → ḢTrans e (Desc.comp D (e j)) (Desc.comp E j)

ḞḢTrans : Category
ḞḢTrans = record
  { Object   = Σ[ I ∈ Set ] Desc I
  ; Morphism = λ { (J , E) (I , D) → record
                   { Carrier = Σ[ e ∈ (J → I) ] FḢTrans e D E
                   ; _≈_ = λ { (e , ts) (f , us) → (e ≐ f) × ((j : J) (h : Ṡ (Desc.comp E j)) → ḢTrans.s (FḢTrans.comp ts j) h ≅ ḢTrans.s (FḢTrans.comp us j) h) }
                   ; isEquivalence = record { refl  = frefl , λ j h → hrefl
                                            ; sym   = λ { (eeq , teqs) → fsym eeq , λ j h → hsym (teqs j h) }
                                            ; trans = λ { (eeq , teqs) (eeq' , teqs') → ftrans eeq eeq' , λ j h → htrans (teqs j h) (teqs' j h) } } } }
  ; _·_ = λ { (e , ts) (f , us) → (e ∘ f) , wrap λ k → FḢTrans.comp ts (f k) ⊡ FḢTrans.comp us k }
  ; id  = id , wrap λ i → ḢTrans-id
  ; id-l   = λ { (e , t) → frefl , λ j h → hrefl }
  ; id-r   = λ { (e , t) → frefl , λ j h → hrefl }
  ; assoc  = λ { (e , t) (f , u) (g , v) → frefl , λ j h → hrefl }
  ; cong-l = λ { {I , D} {J , E} {K , F} {e , t} {f , u} (g , v) (efeq , tueqs) →
                 (λ j → cong g (efeq j)) ,
                 (λ j h → subst (λ i → (h' : Ṡ (Desc.comp E (e j))) (h'' : Ṡ (Desc.comp E i)) → h' ≅ h'' →
                                       ḢTrans.s (FḢTrans.comp v (e j)) h' ≅ ḢTrans.s (FḢTrans.comp v i) h'')
                            (efeq j) (λ { h' .h' hrefl → hrefl }) (ḢTrans.s (FḢTrans.comp t j) h) (ḢTrans.s (FḢTrans.comp u j) h) (tueqs j h)) }
  ; cong-r = λ { (e , t) (fgeq , uveqs) → (λ k → fgeq (e k)) , (λ k h → uveqs (e k) (ḢTrans.s (FḢTrans.comp t k) h)) } }

ḞḢTransF : Functor ḞḢTrans Fun
ḞḢTransF = record
  { object   = proj₁
  ; morphism = proj₁
  ; ≈-respecting    = proj₁
  ; id-preserving   = frefl
  ; comp-preserving = λ _ _ → frefl }

Shape : Functor ḞḢTrans Fam
Shape = record
  { object   = λ { (I , D) → I , Ṡ ∘ Desc.comp D }
  ; morphism = λ { (e , ts) → e , λ {j} → ḢTrans.s (FḢTrans.comp ts j) }
  ; ≈-respecting    = λ { (eeq , tseq) → eeq , λ { {j} h .h hrefl → tseq j h } }
  ; id-preserving   = frefl , λ _ _ → id
  ; comp-preserving = λ f g → frefl , λ { h .h hrefl → hrefl } }

Erase : Functor Ōrn ḞḢTrans
Erase = record
  { object   = id
  ; morphism = λ { {J , E} {I , D} (e , O) → e , wrap λ j → ḢTrans-normal (Orn.comp O (ok j)) }
  ; ≈-respecting    = id
  ; id-preserving   = λ { {I , D} → frefl , λ i h → ≡-to-≅ (trans (erase'-idROrn (Desc.comp D i) (const !) h) (Ḣ-map-preserves-id (Desc.comp D i) h)) }
  ; comp-preserving = λ { {K , F} {J , E} {I , D} (e , O) (f , P) → frefl , λ k h → ≡-to-≅ (erase-Ṡ-scROrn (Orn.comp O (ok (f k))) (Orn.comp P (ok k)) h) } }

Normal : Functor ḞḢTrans Ōrn
Normal = record
  { object   = id
  ; morphism = λ { (e , ts) → e , wrap λ { {._} (ok j) → ḢROrn (FḢTrans.comp ts j) } }
  ; ≈-respecting    = λ { {J , E} {I , D} {e , ts} {f , us} (efeq , tueqs) →
                          efeq , λ j h → ḢROrn-≅ (FḢTrans.comp ts j) (FḢTrans.comp us j) (cong (Desc.comp D) (efeq j)) (tueqs j) h }
  ; id-preserving   = λ { {I , D} → frefl , λ i → ḢROrn-id (Desc.comp D i) }
  ; comp-preserving = λ { (e , ts) (f , us) → frefl , λ k → ḢROrn-comp (FḢTrans.comp ts (f k)) (FḢTrans.comp us k) } }

Normal-Erase-inverse : Iso (Funct Ōrn Ōrn) (Normal ⋆ Erase) (idF Ōrn)
Normal-Erase-inverse = record
  { to   = record { comp = λ { (I , D) → id , idOrn D }
                  ; naturality =  λ { {J , E} {I , D} (e , O) →
                                      OrnEq-trans (O ⊙ idOrn E) O (idOrn D ⊙ normOrn O)
                                        (⊙-id-r O)
                                        (OrnEq-sym (idOrn D ⊙ normOrn O) O
                                           (OrnEq-trans (idOrn D ⊙ normOrn O) (normOrn O) O
                                              (⊙-id-l (normOrn O))
                                              (OrnEq-normal O))) } }
  ; from = record { comp = λ { (I , D) → id , idOrn D }
                  ; naturality = λ { {J , E} {I , D} (e , O) →
                                     OrnEq-trans (normOrn O ⊙ idOrn E) (normOrn O) (idOrn D ⊙ O)
                                       (⊙-id-r (normOrn O))
                                       (OrnEq-trans (normOrn O) O (idOrn D ⊙ O)
                                          (OrnEq-normal O)
                                          (OrnEq-sym (idOrn D ⊙ O) O (⊙-id-l O))) } }
  ; from-to-inverse = λ { (I , D) → ⊙-id-l (idOrn D) }
  ; to-from-inverse = λ { (I , D) → ⊙-id-l (idOrn D) } }

Erase-Normal-inverse : Iso (Funct ḞḢTrans ḞḢTrans) (Erase ⋆ Normal) (idF ḞḢTrans)
Erase-Normal-inverse = record
  { to   = record { comp = λ { (I , D) → id , wrap λ i → ḢTrans-id }
                  ; naturality = λ { (e , ts) → frefl , λ j h → ≡-to-≅ (sym (erase-Ṡ-ḢROrn (FḢTrans.comp ts j) h)) } }
  ; from = record { comp = λ { (I , D) → id , wrap λ i → ḢTrans-id }
                  ; naturality = λ { (e , ts) → frefl , λ j h → ≡-to-≅ (erase-Ṡ-ḢROrn (FḢTrans.comp ts j) h) } }
  ; from-to-inverse = λ { (I , D) → frefl , λ i h → hrefl }
  ; to-from-inverse = λ { (I , D) → frefl , λ i h → hrefl } }

Ōrn-ḞḢTrans-equiv : CatEquiv Ōrn ḞḢTrans
Ōrn-ḞḢTrans-equiv = record
  { to   = Erase
  ; from = Normal
  ; from-to-inverse = Normal-Erase-inverse
  ; to-from-inverse = Erase-Normal-inverse }
