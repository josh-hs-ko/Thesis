-- Horizontal transformations, i.e., shape-altering morphisms between horizontal data (cf. container morphisms).
-- Ornaments can be derived from horizontal transformations.

module Thesis.Ornament.Horizontal where

open import Thesis.Prelude.Category.Isomorphism
open import Thesis.Prelude.Function
open import Thesis.Prelude.Product
open import Thesis.Description
open import Thesis.Description.Horizontal
open import Thesis.Description.HorizontalEquivalence
open import Thesis.Ornament
open import Thesis.Ornament.SequentialComposition
open import Thesis.Ornament.Equivalence

open import Function using (id; _∘_)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; <_,_>; curry; uncurry) renaming (map to _**_)
open import Data.List using (List; []; _∷_)
import Relation.Binary.EqReasoning as EqReasoning
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong) renaming (setoid to ≡-Setoid)
open import Relation.Binary.HeterogeneousEquality using (_≅_; ≡-to-≅; ≅-to-≡)


record ḢTrans {I J : Set} (e : J → I) (D : RDesc I) (E : RDesc J) : Set where
  constructor _,_
  field
    s : Ṡ E → Ṡ D
    c : (hs : Ṡ E) → Ė e (next E hs) (next D (s hs))

ḢTrans-app' :
  {I J : Set} {e : J → I} {D : RDesc I} {E : RDesc J} (t : ḢTrans e D E) {X : I → Set} →
  Σ (Ṡ E) (Ṁ (X ∘ e) ∘ next E) → Σ (Ṡ D) (Ṁ X ∘ next D)
ḢTrans-app' t (hs , xs) = ḢTrans.s t hs , erase-Ṁ (ḢTrans.c t hs) xs

cong-erase-Ṁ :
  {I J : Set} {e : J → I} {is is' : List I} {js : List J} (eqs : Ė e js is) (eqs' : Ė e js is') → is ≡ is' →
  {X : I → Set} (xs : Ṁ (X ∘ e) js) → erase-Ṁ eqs {X} xs ≅ erase-Ṁ eqs' {X} xs
cong-erase-Ṁ []           []            refl _        = ≡-to-≅ refl
cong-erase-Ṁ (refl ∷ eqs) (refl ∷ eqs') refl (x , xs) = ≡-to-≅ (cong (_,_ x) (≅-to-≡ (cong-erase-Ṁ eqs eqs' refl xs)))

cong-ḢTrans-app' :
  {I J : Set} {e : J → I} {D : RDesc I} {E : RDesc J} (t u : ḢTrans e D E) →
  ḢTrans.s t ≐ ḢTrans.s u → {X : I → Set} → ḢTrans-app' t {X} ≐ ḢTrans-app' u {X}
cong-ḢTrans-app' {D = D} t u t≐u (hs , xs) = cong₂-pair (t≐u hs) (cong-erase-Ṁ (ḢTrans.c t hs) (ḢTrans.c u hs) (cong (next D) (t≐u hs)) xs)

ḢTrans-app : {I J : Set} {e : J → I} {D : RDesc I} {E : RDesc J} (f : ḢTrans e D E) {X : I → Set} → ⟦ E ⟧ (X ∘ e) → ⟦ D ⟧ X
ḢTrans-app {e = e} {D} {E} t {X} = Ḣ-comp D (Ṁ X) ∘ ḢTrans-app' t ∘ Ḣ-decomp E (Ṁ (X ∘ e))

ḢTrans-id : {I : Set} {D : RDesc I} → ḢTrans id D D
ḢTrans-id = (λ hs → hs) , (λ hs → Ė-refl)

ḢTrans-comp :
  {I J K : Set} {e : J → I} {f : K → J} {D : RDesc I} {E : RDesc J} {F : RDesc K} → ḢTrans e D E → ḢTrans f E F → ḢTrans (e ∘ f) D F
ḢTrans-comp t u = ḢTrans.s t ∘ ḢTrans.s u , (λ hs → Ė-trans (ḢTrans.c t (ḢTrans.s u hs)) (ḢTrans.c u hs))

erase-after-erase-Ṁ :
  {I J K : Set} {e : J → I} {f : K → J} {is : List I} {js : List J} {ks : List K}
  (eqs : Ė (e ∘ f) ks is) (eqs' : Ė e js is) (eqs'' : Ė f ks js) →
  {X : I → Set} (xs : Ṁ (X ∘ e ∘ f) ks) → erase-Ṁ eqs {X} xs ≡ erase-Ṁ eqs' (erase-Ṁ eqs'' xs)
erase-after-erase-Ṁ []         []            []             xs               = refl
erase-after-erase-Ṁ (eq ∷ eqs) (refl ∷ eqs') (refl ∷ eqs'') (x , xs) with eq
erase-after-erase-Ṁ (eq ∷ eqs) (refl ∷ eqs') (refl ∷ eqs'') (x , xs) | refl  = cong (_,_ x) (erase-after-erase-Ṁ eqs eqs' eqs'' xs)

ḢTrans-app'-comp :
  {I J K : Set} {e : J → I} {f : K → J} {D : RDesc I} {E : RDesc J} {F : RDesc K} (t : ḢTrans e D E) (u : ḢTrans f E F) →
  {X : I → Set} (hsxs : Σ (Ṡ F) (Ṁ (X ∘ e ∘ f) ∘ next F)) → ḢTrans-app' (ḢTrans-comp t u) {X} hsxs ≡ ḢTrans-app' t (ḢTrans-app' u hsxs)
ḢTrans-app'-comp t u (hs , xs) = cong₂-pair refl (≡-to-≅ (erase-after-erase-Ṁ
                                                            (Ė-trans (ḢTrans.c t (ḢTrans.s u hs)) (ḢTrans.c u hs))
                                                            (ḢTrans.c t (ḢTrans.s u hs))
                                                            (ḢTrans.c u hs)
                                                            xs))

ḢROrn-∇ :
  {I J : Set} {e : J → I} {D : RDesc I} {js : List J} → Σ[ hs ∶ Ṡ D ] Ė e js (next D hs) → ROrn e D (ṿ js)
ḢROrn-∇ {D = ṿ is } (hs       , eqs) = ṿ eqs
ḢROrn-∇ {D = σ S D} ((s , hs) , eqs) = ∇ s (ḢROrn-∇ {D = D s} (hs , eqs))

ḢROrn : {I J : Set} {e : J → I} {D : RDesc I} {E : RDesc J} → ḢTrans e D E → ROrn e D E
ḢROrn {E = ṿ js } t = ḢROrn-∇ (ḢTrans.s t tt , ḢTrans.c t tt)
ḢROrn {E = σ S E} t = Δ[ s ∶ S ] ḢROrn {E = E s} (curry (ḢTrans.s t) s , curry (ḢTrans.c t) s)

erase-ḢROrn-∇ :
  {I J : Set} {e : J → I} (D : RDesc I) {js : List J}
  (hs : Ṡ D) (eqs : Ė e js (next D hs)) {X : I → Set} (xs : Ṁ (X ∘ e) js) →
  erase (ḢROrn-∇ {D = D} (hs , eqs)) {X} xs ≡ Iso.from Fun (Ḣ-iso D (Ṁ X)) (hs , erase-Ṁ eqs xs)
erase-ḢROrn-∇ (ṿ is)  hs       eqs xs = refl
erase-ḢROrn-∇ (σ S D) (s , hs) eqs xs = cong₂-pair refl (≡-to-≅ (erase-ḢROrn-∇ (D s) hs eqs xs))

erase-ḢROrn :
  {I J : Set} {e : J → I} {D : RDesc I} {E : RDesc J} (t : ḢTrans e D E) {X : I → Set} (xs : ⟦ E ⟧ (X ∘ e)) →
  erase (ḢROrn t) {X} xs ≡ ḢTrans-app t xs
erase-ḢROrn {D = D} {ṿ js } t xs       = uncurry (erase-ḢROrn-∇ D) (ḢTrans.s t tt , ḢTrans.c t tt) xs
erase-ḢROrn {D = D} {σ S E} t (s , xs) = erase-ḢROrn {D = D} {E s} (curry (ḢTrans.s t) s , curry (ḢTrans.c t) s) xs

ḢROrn-id : {I : Set} {D : RDesc I} → ROrnEq (ḢROrn (ḢTrans-id {I} {D})) (idROrn D)
ḢROrn-id {I} {D} X xs xs' heq with HoriEq-to-≡ D xs xs' heq
ḢROrn-id {I} {D} X xs ._  heq | refl =
  HoriEq-from-≡ D
    (begin
       erase (ḢROrn (ḢTrans-id {I} {D})) xs
         ≡⟨ erase-ḢROrn (ḢTrans-id {I} {D}) xs ⟩
       ḢTrans-app (ḢTrans-id {I} {D}) xs
         ≡⟨ cong (Ḣ-comp D (Ṁ X)) (cong (_,_ _) (erase-idROrn-Ṁ _ _)) ⟩
       Ḣ-comp D (Ṁ X) (Ḣ-decomp D (Ṁ X) xs)
         ≡⟨ Iso.from-to-inverse Fun (Ḣ-iso D (Ṁ X)) xs ⟩
       xs
         ≡⟨ sym (erase-idROrn D) ⟩
       erase (idROrn D) xs
     ∎)
  where open EqReasoning (≡-Setoid _)

ḢROrn-comp :
  {I J K : Set} {e : J → I} {f : K → J} {D : RDesc I} {E : RDesc J} {F : RDesc K}
  (t : ḢTrans e D E) (u : ḢTrans f E F) → ROrnEq (ḢROrn (ḢTrans-comp t u)) (scROrn (ḢROrn t) (ḢROrn u))
ḢROrn-comp {e = e} {f} {D} {E} {F} t u X xs xs' heq with HoriEq-to-≡ F xs xs' heq
ḢROrn-comp {e = e} {f} {D} {E} {F} t u X xs ._  heq | refl =
  HoriEq-from-≡ D
    (begin
       erase (ḢROrn (ḢTrans-comp t u)) xs
         ≡⟨ erase-ḢROrn (ḢTrans-comp t u) xs ⟩
       ḢTrans-app (ḢTrans-comp t u) xs
         ≡⟨ refl ⟩
       (Ḣ-comp D (Ṁ X) ∘ ḢTrans-app' (ḢTrans-comp t u) ∘ Ḣ-decomp F (Ṁ (X ∘ e ∘ f))) xs
         ≡⟨ cong (Ḣ-comp D (Ṁ X)) (ḢTrans-app'-comp t u (Ḣ-decomp F (Ṁ (X ∘ e ∘ f)) xs)) ⟩
       (Ḣ-comp D (Ṁ X) ∘ ḢTrans-app' t ∘ ḢTrans-app' u ∘ Ḣ-decomp F (Ṁ (X ∘ e ∘ f))) xs
         ≡⟨ sym (cong (Ḣ-comp D (Ṁ X) ∘ ḢTrans-app' t)
                      (Iso.to-from-inverse Fun (Ḣ-iso E (Ṁ (X ∘ e))) (ḢTrans-app' u (Ḣ-decomp F (Ṁ (X ∘ e ∘ f)) xs)))) ⟩
       (Ḣ-comp D (Ṁ X) ∘ ḢTrans-app' t ∘ Ḣ-decomp E (Ṁ (X ∘ e)) ∘ Ḣ-comp E (Ṁ (X ∘ e)) ∘ ḢTrans-app' u ∘ Ḣ-decomp F (Ṁ (X ∘ e ∘ f))) xs
         ≡⟨ refl ⟩
       ḢTrans-app t (ḢTrans-app u xs)
         ≡⟨ sym (erase-ḢROrn t (ḢTrans-app u xs)) ⟩
       erase (ḢROrn t) (ḢTrans-app u xs)
         ≡⟨ sym (cong (erase (ḢROrn t)) (erase-ḢROrn u xs)) ⟩
       erase (ḢROrn t) (erase (ḢROrn u) xs)
         ≡⟨ sym (erase-scROrn (ḢROrn t) (ḢROrn u) xs) ⟩
       erase (scROrn (ḢROrn t) (ḢROrn u)) xs
     ∎)
  where open EqReasoning (≡-Setoid _)

ḢROrn-≐ : {I J : Set} {e : J → I} {D : RDesc I} {E : RDesc J} (t u : ḢTrans e D E) → ḢTrans.s t ≐ ḢTrans.s u → ROrnEq (ḢROrn t) (ḢROrn u)
ḢROrn-≐ {e = e} {D} {E} t u t≐u X xs xs' heq with HoriEq-to-≡ E xs xs' heq
ḢROrn-≐ {e = e} {D} {E} t u t≐u X xs .xs heq | refl =
  HoriEq-from-≡ D
    (begin
       erase(ḢROrn t) xs
         ≡⟨ erase-ḢROrn t xs ⟩
       ḢTrans-app t xs
         ≡⟨ refl ⟩
       (Ḣ-comp D (Ṁ X) ∘ ḢTrans-app' t ∘ Ḣ-decomp E (Ṁ (X ∘ e))) xs
         ≡⟨ cong (Ḣ-comp D (Ṁ X)) (cong-ḢTrans-app' t u t≐u (Ḣ-decomp E (Ṁ (X ∘ e)) xs)) ⟩
       (Ḣ-comp D (Ṁ X) ∘ ḢTrans-app' u ∘ Ḣ-decomp E (Ṁ (X ∘ e))) xs
         ≡⟨ refl ⟩
       ḢTrans-app u xs
         ≡⟨ sym (erase-ḢROrn u xs) ⟩
       erase (ḢROrn u) xs
     ∎)
  where open EqReasoning (≡-Setoid _)
