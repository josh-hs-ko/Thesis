-- Horizontal data can be separated into or combined from "shape" and "content" (cf. containers).

module Thesis.Description.Horizontal where

open import Thesis.Prelude.Category.Isomorphism
open import Thesis.Prelude.Function
open import Thesis.Prelude.Product
open import Thesis.Description

open import Function using (id; const)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂) renaming (map to _**_)
open import Data.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Relation.Binary.HeterogeneousEquality using (_≅_; ≡-to-≅) renaming (cong to hcong)


Hori-indices : {I : Set} (D : RDesc I) {X : List I → Set} → Hori D X → List I
Hori-indices (ṿ is)  x        = is
Hori-indices (σ S D) (s , hs) = Hori-indices (D s) hs

Hori-strip : {I : Set} (D : RDesc I) {X : List I → Set} (hs : Hori D X) → X (Hori-indices D hs)
Hori-strip (ṿ is)  x        = x
Hori-strip (σ S D) (s , hs) = Hori-strip (D s) hs

Hori-decomp : {I : Set} (D : RDesc I) (X : List I → Set) (hs : Hori D X) → Σ[ hs' ∶ Hori D (const ⊤) ] X (Hori-indices D hs')
Hori-decomp (ṿ is)  X x        = tt , x
Hori-decomp (σ S D) X (s , hs) = (_,_ s ** id) (Hori-decomp (D s) X hs)

Hori-comp : {I : Set} (D : RDesc I) (X : List I → Set) → Σ[ hs ∶ Hori D (const ⊤) ] X (Hori-indices D hs) → Hori D X
Hori-comp (ṿ is)  X (_        , x) = x
Hori-comp (σ S D) X ((s , hs) , x) = s , Hori-comp (D s) X (hs , x)

Hori-iso : {I : Set} (D : RDesc I) (X : List I → Set) → Iso Fun (Hori D X) (Σ[ hs ∶ Hori D (const ⊤) ] X (Hori-indices D hs))
Hori-iso {I} D X =
  record { to   = Hori-decomp D X
         ; from = Hori-comp   D X
         ; from-to-inverse = comp-decomp-inverse D X
         ; to-from-inverse = decomp-comp-inverse D X }
  where
    comp-decomp-inverse : (D : RDesc I) (X : List I → Set) (hs : Hori D X) → Hori-comp D X (Hori-decomp D X hs) ≡ hs
    comp-decomp-inverse (ṿ is ) X x        = refl
    comp-decomp-inverse (σ S D) X (s , hs) = cong (_,_ s) (comp-decomp-inverse (D s) X hs)
    decomp-comp-inverse :
      (D : RDesc I) (X : List I → Set) (hsx : Σ[ hs ∶ Hori D (const ⊤) ] X (Hori-indices D hs)) → Hori-decomp D X (Hori-comp D X hsx) ≡ hsx
    decomp-comp-inverse (ṿ is)  X (_        , x) = refl
    decomp-comp-inverse (σ S D) X ((s , hs) , x) = cong₂-pair (cong (_,_ s) (cong proj₁ (decomp-comp-inverse (D s) X (hs , x))))
                                                              (hcong proj₂ (≡-to-≅ (decomp-comp-inverse (D s) X (hs , x))))
