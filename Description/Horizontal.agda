-- Horizontal data, which can be separated into "shape" and "core" (cf. containers), and shape equivalence.

module Description.Horizontal where

open import Prelude.Category.Isomorphism
open import Prelude.Function
open import Prelude.Function.Fam
open import Prelude.Product
open import Description

open import Function using (id; const; _∘_)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; Σ-syntax; _,_; proj₁; proj₂) renaming (map to _**_)
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

Ḣ-decomp-Ṡ : {I : Set} (D : RDesc I) (hs : Ṡ D) → Ḣ-decomp D (const ⊤) hs ≡ (hs , tt)
Ḣ-decomp-Ṡ (ṿ is)  _        = refl
Ḣ-decomp-Ṡ (σ S D) (s , hs) = cong (_,_ s ** id) (Ḣ-decomp-Ṡ (D s) hs)

Ḣ-comp-Ṡ : {I : Set} (D : RDesc I) (hs : Ṡ D) → Ḣ-comp D (const ⊤) (hs , tt) ≡ hs
Ḣ-comp-Ṡ (ṿ is)  _        = refl
Ḣ-comp-Ṡ (σ S D) (s , hs) = cong (_,_ s) (Ḣ-comp-Ṡ (D s) hs)

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

Ḣ-map-to-Ḣ-decomp : {I : Set} (D : RDesc I) (X : List I → Set) (hs : Ḣ D X) → Ḣ-map D ! hs ≡ proj₁ (Ḣ-decomp D X hs)
Ḣ-map-to-Ḣ-decomp (ṿ is)  X _        = refl
Ḣ-map-to-Ḣ-decomp (σ S D) X (s , hs) = cong (_,_ s) (Ḣ-map-to-Ḣ-decomp (D s) X hs)

Ḣ-map-preserves-shape :
  {I : Set} (D : RDesc I) (X Y : List I → Set) (f : X ⇉ Y) (xs : Ḣ D X) → proj₁ (Ḣ-decomp D X xs) ≡ proj₁ (Ḣ-decomp D Y (Ḣ-map D f xs))
Ḣ-map-preserves-shape (ṿ is)  X Y f xs       = refl
Ḣ-map-preserves-shape (σ S D) X Y f (s , xs) = cong (_,_ s) (Ḣ-map-preserves-shape (D s) X Y f xs)
