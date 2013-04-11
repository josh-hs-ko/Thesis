-- Horizontal data, which can be separated into "shape" and "core" (cf. containers), and shape equivalence.

module Thesis.Description.Horizontal where

open import Thesis.Prelude.Category.Isomorphism
open import Thesis.Prelude.Function
open import Thesis.Prelude.Product
open import Thesis.Description

open import Function using (id; const; _∘_)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂) renaming (map to _**_)
open import Data.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Relation.Binary.HeterogeneousEquality using (_≅_; ≡-to-≅) renaming (cong to hcong)


next : {I : Set} (D : RDesc I) {X : List I → Set} → Ḣ D X → List I
next (ṿ is)  x        = is
next (σ S D) (s , hs) = next (D s) hs

core : {I : Set} (D : RDesc I) {X : List I → Set} (hs : Ḣ D X) → X (next D hs)
core (ṿ is)  x        = x
core (σ S D) (s , hs) = core (D s) hs

Ṡ : {I : Set} → RDesc I → Set
Ṡ D = Ḣ D (const ⊤)

Ḣ-decomp : {I : Set} (D : RDesc I) (X : List I → Set) (hs : Ḣ D X) → Σ (Ṡ D) (X ∘ next D)
Ḣ-decomp (ṿ is)  X x        = tt , x
Ḣ-decomp (σ S D) X (s , hs) = (_,_ s ** id) (Ḣ-decomp (D s) X hs)

Ḣ-comp : {I : Set} (D : RDesc I) (X : List I → Set) → Σ (Ṡ D) (X ∘ next D) → Ḣ D X
Ḣ-comp (ṿ is)  X (_        , x) = x
Ḣ-comp (σ S D) X ((s , hs) , x) = s , Ḣ-comp (D s) X (hs , x)

Ḣ-iso : {I : Set} (D : RDesc I) (X : List I → Set) → Iso Fun (Ḣ D X) (Σ (Ṡ D) (X ∘ next D))
Ḣ-iso {I} D X =
  record { to   = Ḣ-decomp D X
         ; from = Ḣ-comp   D X
         ; from-to-inverse = comp-decomp-inverse D X
         ; to-from-inverse = decomp-comp-inverse D X }
  where
    comp-decomp-inverse : (D : RDesc I) (X : List I → Set) (hs : Ḣ D X) → Ḣ-comp D X (Ḣ-decomp D X hs) ≡ hs
    comp-decomp-inverse (ṿ is ) X x        = refl
    comp-decomp-inverse (σ S D) X (s , hs) = cong (_,_ s) (comp-decomp-inverse (D s) X hs)
    decomp-comp-inverse :
      (D : RDesc I) (X : List I → Set) (hsx : Σ (Ṡ D) (X ∘ next D)) → Ḣ-decomp D X (Ḣ-comp D X hsx) ≡ hsx
    decomp-comp-inverse (ṿ is)  X (_        , x) = refl
    decomp-comp-inverse (σ S D) X ((s , hs) , x) = cong₂-pair (cong (_,_ s) (cong proj₁ (decomp-comp-inverse (D s) X (hs , x))))
                                                              (hcong proj₂ (≡-to-≅ (decomp-comp-inverse (D s) X (hs , x))))

data ṠEq {I : Set} : (D : RDesc I) → Ṡ D → (E : RDesc I) → Ṡ E → Set₁ where
  ṿ : {is is' : List I} → ṠEq (ṿ is) tt (ṿ is') tt
  σ : {S : Set} (s : S) {D : S → RDesc I} {hs : Ṡ (D s)} {E : S → RDesc I} {hs' : Ṡ (E s)} →
      ṠEq (D s) hs (E s) hs' → ṠEq (σ S D) (s , hs) (σ S E) (s , hs')

ṠEq-refl : {I : Set} {D : RDesc I} {hs : Ṡ D} → ṠEq D hs D hs
ṠEq-refl {I} {D = ṿ is }          = ṿ
ṠEq-refl {I} {D = σ S D} {s , hs} = σ s (ṠEq-refl)

ṠEq-sym : {I : Set} {D E : RDesc I} {hs : Ṡ D} {hs' : Ṡ E} → ṠEq D hs E hs' → ṠEq E hs' D hs
ṠEq-sym ṿ         = ṿ
ṠEq-sym (σ s seq) = σ s (ṠEq-sym seq)

ṠEq-trans : {I : Set} {D E F : RDesc I} {hs : Ṡ D} {hs' : Ṡ E} {hs'' : Ṡ F} → ṠEq D hs E hs' → ṠEq E hs' F hs'' → ṠEq D hs F hs''
ṠEq-trans ṿ         ṿ           = ṿ
ṠEq-trans (σ s seq) (σ .s seq') = σ s (ṠEq-trans seq seq')

ṠEq-to-≡ : {I : Set} {D : RDesc I} {xs xs' : Ṡ D} → ṠEq D xs D xs' → xs ≡ xs'
ṠEq-to-≡ ṿ         = refl
ṠEq-to-≡ (σ s seq) = cong (_,_ s) (ṠEq-to-≡ seq)

ṠEq-from-≡ : {I : Set} {D : RDesc I} {xs xs' : Ṡ D} → xs ≡ xs' → ṠEq D xs D xs'
ṠEq-from-≡ {I} {ṿ is }                     eq        = ṿ
ṠEq-from-≡ {I} {σ S D} {s , xs} {s' , xs'} eq with cong proj₁ eq
ṠEq-from-≡ {I} {σ S D} {s , xs} {.s , xs'} eq | refl = σ s (ṠEq-from-≡ (cong-proj₂ eq))
