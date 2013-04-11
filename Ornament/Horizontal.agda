-- Horizontal transformations, i.e., shape-altering morphisms between horizontal data (cf. container morphisms).
-- Ornaments can be derived from horizontal transformations.

module Thesis.Ornament.Horizontal where

open import Thesis.Prelude.Category.Isomorphism
open import Thesis.Prelude.InverseImage
open import Thesis.Prelude.Function
open import Thesis.Prelude.Product
open import Thesis.Description
open import Thesis.Description.Horizontal
open import Thesis.Ornament

open import Function using (id; const; _∘_)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_; <_,_>; curry; uncurry) renaming (map to _**_)
open import Data.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst; module ≡-Reasoning)
open import Relation.Binary.HeterogeneousEquality using (_≅_; ≡-to-≅; ≅-to-≡) renaming (refl to hrefl; cong to hcong; cong₂ to hcong₂)


record ḢTrans {I J : Set} (e : J → I) (D : RDesc I) (E : RDesc J) : Set where
  constructor _,_
  field
    s : Ṡ E → Ṡ D
    c : (hs : Ṡ E) → Ė e (next E hs) (next D (s hs))

ḢTrans-app' :
  {I J : Set} {e : J → I} {D : RDesc I} {E : RDesc J} (t : ḢTrans e D E) {X : I → Set} →
  Σ (Ṡ E) (Ṁ (X ∘ e) ∘ next E) → Σ (Ṡ D) (Ṁ X ∘ next D)
ḢTrans-app' t (hs , xs) = ḢTrans.s t hs , erase-Ṁ (ḢTrans.c t hs) xs

ṀHEq : {I : Set} {X Y : I → Set} (is : List I) → Ṁ X is → Ṁ Y is → Set
ṀHEq is xs ys = All-Ṁ (λ _ xy → proj₁ xy ≅ proj₂ xy) is (Ṁ-comp is xs ys)

cong-erase-Ṁ :
  {I J : Set} {e e' : J → I} {is is' : List I} {js : List J} (eqs : Ė e js is) (eqs' : Ė e' js is') → is ≡ is' →
  {X : I → Set} (xs : Ṁ (X ∘ e) js) (xs' : Ṁ (X ∘ e') js) → ṀHEq js xs xs' → erase-Ṁ {X = X} eqs xs ≅ erase-Ṁ {X = X} eqs' xs'
cong-erase-Ṁ         []                 []            refl _        _          _                     = hrefl
cong-erase-Ṁ {e = e} (_∷_ {j} refl eqs) (refl ∷ eqs') iseq (x , xs) (x' , xs') (heq , heqs) with e j
cong-erase-Ṁ {e = e} (_∷_ {j} refl eqs) (refl ∷ eqs') refl (x , xs) (.x , xs') (hrefl , heqs) | ._   =
  ≡-to-≅ (cong (_,_ x) (≅-to-≡ (cong-erase-Ṁ eqs eqs' refl xs xs' heqs)))

cong-ḢTrans-app' :
  {I J : Set} {e e' : J → I} {D : RDesc I} {E : RDesc J} (t : ḢTrans e D E) (u : ḢTrans e' D E) →
  e ≐ e' → ḢTrans.s t ≐ ḢTrans.s u → (hs : Ṡ E) {X : I → Set} (xs : Ṁ (X ∘ e) (next E hs)) (xs' : Ṁ (X ∘ e') (next E hs)) →
  ṀHEq (next E hs) xs xs' → ḢTrans-app' t {X} (hs , xs) ≡ ḢTrans-app' u {X} (hs , xs')
cong-ḢTrans-app' {D = D} t u e≐e' t≐u hs xs xs' heq =
  cong₂-pair (t≐u hs) (cong-erase-Ṁ (ḢTrans.c t hs) (ḢTrans.c u hs) (cong (next D) (t≐u hs)) xs xs' heq)

ḢTrans-app : {I J : Set} {e : J → I} {D : RDesc I} {E : RDesc J} (f : ḢTrans e D E) {X : I → Set} → ⟦ E ⟧ (X ∘ e) → ⟦ D ⟧ X
ḢTrans-app {e = e} {D} {E} t {X} = Ḣ-comp D (Ṁ X) ∘ ḢTrans-app' t ∘ Ḣ-decomp E (Ṁ (X ∘ e))

ḢTrans-id : {I : Set} {D : RDesc I} → ḢTrans id D D
ḢTrans-id = (λ hs → hs) , (λ hs → Ė-refl)

_⊡_ : {I J K : Set} {e : J → I} {f : K → J} {D : RDesc I} {E : RDesc J} {F : RDesc K} → ḢTrans e D E → ḢTrans f E F → ḢTrans (e ∘ f) D F
t ⊡ u = ḢTrans.s t ∘ ḢTrans.s u , (λ hs → Ė-trans (ḢTrans.c t (ḢTrans.s u hs)) (ḢTrans.c u hs))

erase-after-erase-Ṁ :
  {I J K : Set} {e : J → I} {f : K → J} {is : List I} {js : List J} {ks : List K}
  (eqs : Ė (e ∘ f) ks is) (eqs' : Ė e js is) (eqs'' : Ė f ks js) →
  {X : I → Set} (xs : Ṁ (X ∘ e ∘ f) ks) → erase-Ṁ {X = X} eqs xs ≡ erase-Ṁ eqs' (erase-Ṁ eqs'' xs)
erase-after-erase-Ṁ []         []            []             xs               = refl
erase-after-erase-Ṁ (eq ∷ eqs) (refl ∷ eqs') (refl ∷ eqs'') (x , xs) with eq
erase-after-erase-Ṁ (eq ∷ eqs) (refl ∷ eqs') (refl ∷ eqs'') (x , xs) | refl  = cong (_,_ x) (erase-after-erase-Ṁ eqs eqs' eqs'' xs)

ḢTrans-app'-comp :
  {I J K : Set} {e : J → I} {f : K → J} {D : RDesc I} {E : RDesc J} {F : RDesc K} (t : ḢTrans e D E) (u : ḢTrans f E F) →
  {X : I → Set} (hsxs : Σ (Ṡ F) (Ṁ (X ∘ e ∘ f) ∘ next F)) → ḢTrans-app' (t ⊡ u) {X} hsxs ≡ ḢTrans-app' t (ḢTrans-app' u hsxs)
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

{-

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
  where open ≡-Reasoning

ḢROrn-comp : {I J K : Set} {e : J → I} {f : K → J} {D : RDesc I} {E : RDesc J} {F : RDesc K}
             (t : ḢTrans e D E) (u : ḢTrans f E F) → ROrnEq (ḢROrn (t ⊡ u)) (scROrn (ḢROrn t) (ḢROrn u))
ḢROrn-comp {e = e} {f} {D} {E} {F} t u X xs xs' heq with HoriEq-to-≡ F xs xs' heq
ḢROrn-comp {e = e} {f} {D} {E} {F} t u X xs ._  heq | refl =
  HoriEq-from-≡ D
    (begin
       erase (ḢROrn (t ⊡ u)) xs
         ≡⟨ erase-ḢROrn (t ⊡ u) xs ⟩
       ḢTrans-app (t ⊡ u) xs
         ≡⟨ refl ⟩
       (Ḣ-comp D (Ṁ X) ∘ ḢTrans-app' (t ⊡ u) ∘ Ḣ-decomp F (Ṁ (X ∘ e ∘ f))) xs
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
  where open ≡-Reasoning

ḢROrn-≐ : {I J : Set} {e e' : J → I} {D : RDesc I} {E : RDesc J} (t : ḢTrans e D E) (u : ḢTrans e' D E) →
          e ≐ e' → ḢTrans.s t ≐ ḢTrans.s u → ROrnEq (ḢROrn t) (ḢROrn u)
ḢROrn-≐ {e = e} {e'} {D} {E} t u e≐e' t≐u X xs xs' heq =
  HoriEq-from-≡ D
    (begin
       erase (ḢROrn t) xs
         ≡⟨ erase-ḢROrn t xs ⟩
       ḢTrans-app t xs
         ≡⟨ refl ⟩
       (Ḣ-comp D (Ṁ X) ∘ ḢTrans-app' t ∘ Ḣ-decomp E (Ṁ (X ∘ e))) xs
         ≡⟨ cong (Ḣ-comp D (Ṁ X)) see-below ⟩
       (Ḣ-comp D (Ṁ X) ∘ ḢTrans-app' u ∘ Ḣ-decomp E (Ṁ (X ∘ e'))) xs'
         ≡⟨ refl ⟩
       ḢTrans-app u xs'
         ≡⟨ sym (erase-ḢROrn u xs') ⟩
       erase (ḢROrn u) xs'
     ∎)
  where
    open ≡-Reasoning
    lemma : {I : Set} (D : RDesc I) (X Y : I → Set) (xs : ⟦ D ⟧ X) (ys : ⟦ D ⟧ Y) → HoriEq D xs D ys →
            Σ[ hs ∶ Ṡ D ] Σ[ xs' ∶ Ṁ X (next D hs) ] Σ[ ys' ∶ Ṁ Y (next D hs) ]
               Ḣ-decomp D (Ṁ X) xs ≡ (hs , xs')  ×  Ḣ-decomp D (Ṁ Y) ys ≡ (hs , ys')  ×  ṀHEq (next D hs) xs' ys'
    lemma .(ṿ is)  X Y xs        ys        (ṿ {is} heq)                     = tt , xs , ys , refl , refl , heq
    lemma .(σ S D) X Y .(s , xs) .(s , ys) (σ {S} s {D} {.D} {xs} {ys} heq) =
      (_,_ s ** (id ** (id ** (cong (_,_ s ** id) ** (cong (_,_ s ** id) ** id))))) (lemma (D s) X Y xs ys heq)
    see-below : ḢTrans-app' t {X} (Ḣ-decomp E (Ṁ (X ∘ e)) xs) ≡ ḢTrans-app' u {X} (Ḣ-decomp E (Ṁ (X ∘ e')) xs')
    see-below with lemma E (X ∘ e) (X ∘ e') xs xs' heq
    see-below | hs , xs'' , xs''' , eq , eq' , heq' =
      trans (cong (ḢTrans-app' t {X}) eq) (trans (cong-ḢTrans-app' t u e≐e' t≐u hs xs'' xs''' heq') (sym (cong (ḢTrans-app' u {X}) eq')))

-}

normal-coherence :
  {I J : Set} {e : J → I} {D : RDesc I} {E : RDesc J} (O : ROrn e D E) {X : List J → Set} {Y : List I → Set}
  (f : {is : List I} {js : List J} → Ė e js is → X js → Y is) (hs : Ḣ E X) → Ė e (next E hs) (next D (erase' O f hs))
normal-coherence (ṿ eqs) f hs       = eqs
normal-coherence (σ S O) f (s , hs) = normal-coherence (O s) f hs
normal-coherence (Δ T O) f (t , hs) = normal-coherence (O t) f hs
normal-coherence (∇ s O) f hs       = normal-coherence O f hs

ḢTrans-normal : {I J : Set} {e : J → I} {D : RDesc I} {E : RDesc J} (O : ROrn e D E) → ḢTrans e D E
ḢTrans-normal O = erase' O (const !) , normal-coherence O (const !)

normROrn : {I J : Set} {e : J → I} {D : RDesc I} {E : RDesc J} → ROrn e D E → ROrn e D E
normROrn O = ḢROrn (ḢTrans-normal O)

ḢTrans-app-normal :
  {I J : Set} {e : J → I} {D : RDesc I} {E : RDesc J} (O : ROrn e D E) → {X : I → Set} → ḢTrans-app (ḢTrans-normal O) ≐ erase O {X}
ḢTrans-app-normal (ṿ eqs) xs       = refl
ḢTrans-app-normal (σ S O) (s , xs) = cong (_,_ s) (ḢTrans-app-normal (O s) xs)
ḢTrans-app-normal (Δ T O) (t , xs) = ḢTrans-app-normal (O t) xs
ḢTrans-app-normal (∇ s O) xs       = cong (_,_ s) (ḢTrans-app-normal O xs)

{-

ROrnEq-normal : {I J : Set} {e : J → I} {D : RDesc I} {E : RDesc J} (O : ROrn e D E) → ROrnEq (normROrn O) O
ROrnEq-normal {D = D} {E} O X xs xs' heq with HoriEq-to-≡ E xs xs' heq
ROrnEq-normal {D = D} {E} O X xs .xs heq | refl =
  HoriEq-from-≡ D
    (begin
       erase (normROrn O) xs
         ≡⟨ erase-ḢROrn (ḢTrans-normal O) xs ⟩
       ḢTrans-app (ḢTrans-normal O) xs
         ≡⟨ ḢTrans-app-normal O xs ⟩
       erase O xs
     ∎)
  where open ≡-Reasoning

normOrn : {I J : Set} {e : J → I} {D : Desc I} {E : Desc J} → Orn e D E → Orn e D E
normOrn (wrap O) = wrap (normROrn ∘ O)

OrnEq-normal : {I J : Set} {e : J → I} {D : Desc I} {E : Desc J} (O : Orn e D E) → OrnEq (normOrn O) O
OrnEq-normal (wrap O) = frefl , (λ j → ROrnEq-normal (O (ok j)))

-}
