-- Ornamental equivalences about horizontal ornaments.

module Ornament.Horizontal.Equivalence where

open import Prelude.Category.Isomorphism
open import Prelude.Function
open import Prelude.InverseImage
open import Description
open import Description.Horizontal
open import Ornament
open import Ornament.SequentialComposition
open import Ornament.Horizontal
open import Ornament.Equivalence

open import Function using (const)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; Σ-syntax; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; cong₂; module ≡-Reasoning)
open import Relation.Binary.HeterogeneousEquality using (_≅_; ≡-to-≅; ≅-to-≡)


ḢROrn-id : {I : Set} (D : RDesc I) → ROrnEq (ḢROrn (ḢTrans-id {I} {D})) (idROrn D)
ḢROrn-id {I} D hs =
  ≡-to-≅ (begin
            erase-Ṡ (ḢROrn (ḢTrans-id {I} {D})) hs
              ≡⟨ erase'-ḢROrn (ḢTrans-id {I} {D}) (const !) hs ⟩
            ḢTrans-app (ḢTrans-id {I} {D}) (const !) hs
              ≡⟨ refl ⟩
            Ḣ-comp D (const ⊤) (Ḣ-decomp D (const ⊤) hs)
              ≡⟨ Iso.from-to-inverse (Ḣ-iso D (const ⊤)) hs ⟩
            hs
              ≡⟨ sym (Ḣ-map-preserves-id D hs) ⟩
            Ḣ-map D ! hs
              ≡⟨ sym (erase'-idROrn D (const !) hs) ⟩
            erase-Ṡ (idROrn D) hs
          ∎)
  where open ≡-Reasoning

ḢROrn-comp : {I J K : Set} {e : J → I} {f : K → J} {D : RDesc I} {E : RDesc J} {F : RDesc K}
             (t : ḢTrans e D E) (u : ḢTrans f E F) → ROrnEq (ḢROrn (t ⊡ u)) (scROrn (ḢROrn t) (ḢROrn u))
ḢROrn-comp {e = e} {f} {D} {E} {F} t u hs =
  ≡-to-≅ (begin
            erase-Ṡ (ḢROrn (t ⊡ u)) hs
              ≡⟨ erase'-ḢROrn (t ⊡ u) (const !) hs ⟩
            ḢTrans-app (t ⊡ u) (const !) hs
              ≡⟨ ḢTrans-app-comp t u hs ⟩
            ḢTrans-app t (const !) (ḢTrans-app u (const !) hs)
              ≡⟨ sym (erase'-ḢROrn t (const !) (ḢTrans-app u (const !) hs)) ⟩
            erase-Ṡ (ḢROrn t) (ḢTrans-app u (const !) hs)
              ≡⟨ sym (cong (erase-Ṡ (ḢROrn t)) (erase'-ḢROrn u (const !) hs)) ⟩
            erase-Ṡ (ḢROrn t) (erase-Ṡ (ḢROrn u) hs)
              ≡⟨ sym (erase-Ṡ-scROrn (ḢROrn t) (ḢROrn u) hs) ⟩
            erase-Ṡ (scROrn (ḢROrn t) (ḢROrn u)) hs
          ∎)
  where open ≡-Reasoning

ḢROrn-≐ : {I J : Set} {e e' : J → I} {D : RDesc I} {E : RDesc J} (t : ḢTrans e D E) (u : ḢTrans e' D E) →
          ḢTrans.s t ≐ ḢTrans.s u → ROrnEq (ḢROrn t) (ḢROrn u)
ḢROrn-≐ {D = D} {E} t u t≐u hs =
  ≡-to-≅ (begin
            erase-Ṡ (ḢROrn t) hs
              ≡⟨ erase'-ḢROrn t (const !) hs ⟩
            ḢTrans-app t (const !) hs
              ≡⟨ cong (Ḣ-comp D (const ⊤)) (cong₂ _,_ (t≐u (proj₁ (Ḣ-decomp E (const ⊤) hs))) refl) ⟩
            ḢTrans-app u (const !) hs
              ≡⟨ sym (erase'-ḢROrn u (const !) hs) ⟩
            erase-Ṡ (ḢROrn u) hs
          ∎)
  where open ≡-Reasoning

ḢROrn-≅ : {I J : Set} {e e' : J → I} {D D' : RDesc I} {E : RDesc J} (t : ḢTrans e D E) (u : ḢTrans e' D' E) →
          D ≡ D' → ((h : Ṡ E) → ḢTrans.s t h ≅ ḢTrans.s u h) → ROrnEq (ḢROrn t) (ḢROrn u)
ḢROrn-≅ t u refl t≅u = ḢROrn-≐ t u (λ hs → ≅-to-≡ (t≅u hs))

ROrnEq-normal : {I J : Set} {e : J → I} {D : RDesc I} {E : RDesc J} (O : ROrn e D E) → ROrnEq (normROrn O) O
ROrnEq-normal {D = D} {E} O hs =
  ≡-to-≅ (begin
            erase-Ṡ (normROrn O) hs
              ≡⟨ erase'-ḢROrn (ḢTrans-normal O) (const !) hs ⟩
            ḢTrans-app (ḢTrans-normal O) (const !) hs
              ≡⟨ ḢTrans-app-normal O (const !) hs ⟩
            erase-Ṡ O hs
          ∎)
  where open ≡-Reasoning

OrnEq-normal : {I J : Set} {e : J → I} {D : Desc I} {E : Desc J} (O : Orn e D E) → OrnEq (normOrn O) O
OrnEq-normal (wrap O) = frefl , λ j → ROrnEq-normal (O (ok j))
