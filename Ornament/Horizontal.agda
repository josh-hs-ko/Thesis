-- Horizontal transformations, i.e., shape-altering morphisms between horizontal data (cf. container morphisms).
-- Ornaments can be derived from horizontal transformations.

module Ornament.Horizontal where

open import Prelude.Category.Isomorphism
open import Prelude.InverseImage
open import Prelude.Function
open import Prelude.Product
open import Description
open import Description.Horizontal
open import Ornament

open import Function using (id; flip; const; _∘_)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; Σ-syntax; _,_; proj₁; proj₂; _×_; <_,_>; curry; uncurry) renaming (map to _**_)
open import Data.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst; module ≡-Reasoning)
open import Relation.Binary.HeterogeneousEquality using (_≅_; ≡-to-≅; ≅-to-≡) renaming (refl to hrefl; cong to hcong; cong₂ to hcong₂)


record ḢTrans {I J : Set} (e : J → I) (D : RDesc I) (E : RDesc J) : Set where
  constructor _,_
  field
    s : Ṡ E → Ṡ D
    c : (hs : Ṡ E) → Ė e (next E hs) (next D (s hs))

ḢTrans-id : {I : Set} {D : RDesc I} → ḢTrans id D D
ḢTrans-id = id , λ _ → Ė-refl

_⊡_ : {I J K : Set} {e : J → I} {f : K → J} {D : RDesc I} {E : RDesc J} {F : RDesc K} → ḢTrans e D E → ḢTrans f E F → ḢTrans (e ∘ f) D F
t ⊡ u = ḢTrans.s t ∘ ḢTrans.s u , λ hs → Ė-trans (ḢTrans.c t (ḢTrans.s u hs)) (ḢTrans.c u hs)

ḢTrans-app' : {I J : Set} {e : J → I} {D : RDesc I} {E : RDesc J} (t : ḢTrans e D E)
              {X : List I → Set} {Y : List J → Set} → Erasure e Y X → Σ (Ṡ E) (Y ∘ next E) → Σ (Ṡ D) (X ∘ next D)
ḢTrans-app' t f (hs , y) = ḢTrans.s t hs , f (ḢTrans.c t hs) y

cong-ḢTrans-app'-erase-Ṗ :
  {I J : Set} {e e' : J → I} {D : RDesc I} {E : RDesc J} (t : ḢTrans e D E) (u : ḢTrans e' D E) →
  e ≐ e' → ḢTrans.s t ≐ ḢTrans.s u → (hs : Ṡ E) {X : I → Set} (xs : Ṗ (next E hs) (X ∘ e)) (xs' : Ṗ (next E hs) (X ∘ e')) →
  ṖHEq (next E hs) xs xs' → ḢTrans-app' t {flip Ṗ X} erase-Ṗ (hs , xs) ≡ ḢTrans-app' u {flip Ṗ X} erase-Ṗ (hs , xs')
cong-ḢTrans-app'-erase-Ṗ {D = D} t u e≐e' t≐u hs xs xs' heq =
  cong₂-pair (t≐u hs) (cong-erase-Ṗ (ḢTrans.c t hs) (ḢTrans.c u hs) (cong (next D) (t≐u hs)) xs xs' heq)

ḢTrans-app : {I J : Set} {e : J → I} {D : RDesc I} {E : RDesc J} (t : ḢTrans e D E)
             {X : List I → Set} {Y : List J → Set} → Erasure e Y X → Ḣ E Y → Ḣ D X
ḢTrans-app {e = e} {D} {E} t {X} {Y} f = Ḣ-comp D X ∘ ḢTrans-app' t f ∘ Ḣ-decomp E Y

ḢTrans-app-comp :
  {I J K : Set} {e : J → I} {f : K → J} {D : RDesc I} {E : RDesc J} {F : RDesc K} (t : ḢTrans e D E) (u : ḢTrans f E F) →
  ḢTrans-app (t ⊡ u) {const ⊤} {const ⊤} (const !) ≐ ḢTrans-app t (const !) ∘ ḢTrans-app u (const !)
ḢTrans-app-comp {D = D} {E} {F} t u hs =
  cong (Ḣ-comp D (const ⊤))
       (cong₂ _,_ (cong (ḢTrans.s t)
                        (cong proj₁ (sym (Iso.to-from-inverse (Ḣ-iso E (const ⊤)) (ḢTrans.s u (proj₁ (Ḣ-decomp F (const ⊤) hs)) , tt)))))
                  refl)

ḢROrn-∇ : {I J : Set} {e : J → I} {D : RDesc I} {js : List J} → Σ[ hs ∈ Ṡ D ] Ė e js (next D hs) → ROrn e D (ṿ js)
ḢROrn-∇ {D = ṿ is } (hs       , eqs) = ṿ eqs
ḢROrn-∇ {D = σ S D} ((s , hs) , eqs) = ∇ s (ḢROrn-∇ {D = D s} (hs , eqs))

ḢROrn : {I J : Set} {e : J → I} {D : RDesc I} {E : RDesc J} → ḢTrans e D E → ROrn e D E
ḢROrn {E = ṿ js } t = ḢROrn-∇ (ḢTrans.s t tt , ḢTrans.c t tt)
ḢROrn {E = σ S E} t = Δ[ s ∈ S ] ḢROrn {E = E s} (curry (ḢTrans.s t) s , curry (ḢTrans.c t) s)

erase'-ḢROrn-∇ : {I J : Set} {e : J → I} (D : RDesc I) {js : List J}
                 (hs : Ṡ D) (eqs : Ė e js (next D hs)) {X : List I → Set} {Y : List J → Set} (f : Erasure e Y X) →
                 (y : Y js) → erase' (ḢROrn-∇ {D = D} (hs , eqs)) f y ≡ Ḣ-comp D X (hs , f eqs y)
erase'-ḢROrn-∇ (ṿ is)  hs       eqs f y = refl
erase'-ḢROrn-∇ (σ S D) (s , hs) eqs f y = cong₂-pair refl (≡-to-≅ (erase'-ḢROrn-∇ (D s) hs eqs f y))

erase'-ḢROrn : {I J : Set} {e : J → I} {D : RDesc I} {E : RDesc J} (t : ḢTrans e D E)
               {X : List I → Set} {Y : List J → Set} (f : Erasure e Y X) → erase' (ḢROrn t) f ≐ ḢTrans-app t f
erase'-ḢROrn {D = D} {ṿ js } t f y       = erase'-ḢROrn-∇ D (ḢTrans.s t tt) (ḢTrans.c t tt) f y
erase'-ḢROrn {D = D} {σ S E} t f (s , y) = erase'-ḢROrn {D = D} {E s} (curry (ḢTrans.s t) s , curry (ḢTrans.c t) s) f y

erase-Ṡ-ḢROrn : {I J : Set} {e : J → I} {D : RDesc I} {E : RDesc J} (t : ḢTrans e D E) → erase-Ṡ (ḢROrn t) ≐ ḢTrans.s t
erase-Ṡ-ḢROrn {D = D} {E} t hs =
  begin
    erase-Ṡ (ḢROrn t) hs
      ≡⟨ erase'-ḢROrn t (const !) hs ⟩
    ḢTrans-app t (const !) hs
      ≡⟨ Ḣ-comp-Ṡ D (ḢTrans.s t (proj₁ (Ḣ-decomp E (const ⊤) hs))) ⟩
    ḢTrans.s t (proj₁ (Ḣ-decomp E (const ⊤) hs))
      ≡⟨ cong (ḢTrans.s t) (cong proj₁ (Ḣ-decomp-Ṡ E hs)) ⟩
    ḢTrans.s t hs
  ∎
  where open ≡-Reasoning

normal-coherence :
  {I J : Set} {e : J → I} {D : RDesc I} {E : RDesc J} (O : ROrn e D E) {X : List J → Set} {Y : List I → Set}
  (f : Erasure e X Y) (hs : Ḣ E X) → Ė e (next E hs) (next D (erase' O f hs))
normal-coherence (ṿ eqs) f hs       = eqs
normal-coherence (σ S O) f (s , hs) = normal-coherence (O s) f hs
normal-coherence (Δ T O) f (t , hs) = normal-coherence (O t) f hs
normal-coherence (∇ s O) f hs       = normal-coherence O f hs

ḢTrans-normal : {I J : Set} {e : J → I} {D : RDesc I} {E : RDesc J} (O : ROrn e D E) → ḢTrans e D E
ḢTrans-normal O = erase-Ṡ O , normal-coherence O (const !)

ḢTrans-app-normal :
  {I J : Set} {e : J → I} {D : RDesc I} {E : RDesc J} (O : ROrn e D E)
  {X : List I → Set} {Y : List J → Set} (f : Erasure e Y X) → ḢTrans-app (ḢTrans-normal O) f ≐ erase' O {X} f
ḢTrans-app-normal (ṿ eqs) f y        = refl
ḢTrans-app-normal (σ S O) f (s , ys) = cong (_,_ s) (ḢTrans-app-normal (O s) f ys)
ḢTrans-app-normal (Δ T O) f (t , ys) = ḢTrans-app-normal (O t) f ys
ḢTrans-app-normal (∇ s O) f ys       = cong (_,_ s) (ḢTrans-app-normal O f ys)

normROrn : {I J : Set} {e : J → I} {D : RDesc I} {E : RDesc J} → ROrn e D E → ROrn e D E
normROrn O = ḢROrn (ḢTrans-normal O)

normOrn : {I J : Set} {e : J → I} {D : Desc I} {E : Desc J} → Orn e D E → Orn e D E
normOrn (wrap O) = wrap (normROrn ∘ O)
