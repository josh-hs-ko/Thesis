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

open import Function using (id; const; _∘_)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; curry; uncurry)
open import Data.List using (List; []; _∷_)
import Relation.Binary.EqReasoning as EqReasoning
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong) renaming (setoid to ≡-Setoid)
open import Relation.Binary.HeterogeneousEquality using (_≅_; ≡-to-≅)


record HoriTrans {I J : Set} (e : J → I) (D : RDesc I) (E : RDesc J) : Set where
  constructor wrap
  field
    comp : (hs : Hori E (const ⊤)) → Σ[ hs' ∶ Hori D (const ⊤) ] Ė e (Hori-indices E hs) (Hori-indices D hs')

HoriTrans-app : {I J : Set} {e : J → I} {D : RDesc I} {E : RDesc J} (f : HoriTrans e D E) {X : I → Set} (xs : ⟦ E ⟧ (X ∘ e)) → ⟦ D ⟧ X
HoriTrans-app {e = e} {D} {E} f {X} xs = let (hs  , xs') = Hori-decomp E (Ṁ (X ∘ e)) xs
                                             (hs' , eqs) = HoriTrans.comp f hs
                                         in  Hori-comp D (Ṁ X) (hs' , erase-Ṁ eqs xs')

HoriTrans-id : {I : Set} {D : RDesc I} → HoriTrans id D D
HoriTrans-id = wrap λ hs → hs , Ė-refl

HoriTrans-comp :
  {I J K : Set} {e : J → I} {f : K → J} {D : RDesc I} {E : RDesc J} {F : RDesc K} →
  HoriTrans e D E → HoriTrans f E F → HoriTrans (e ∘ f) D F
HoriTrans-comp (wrap g) (wrap h) = wrap λ hs → proj₁ (g (proj₁ (h hs))) , Ė-trans (proj₂ (g (proj₁ (h hs)))) (proj₂ (h hs))

horiROrn-∇ :
  {I J : Set} {e : J → I} {D : RDesc I} {js : List J} → Σ[ hs ∶ Hori D (const ⊤) ] Ė e js (Hori-indices D hs) → ROrn e D (ṿ js)
horiROrn-∇ {D = ṿ is } (hs       , eqs) = ṿ eqs
horiROrn-∇ {D = σ S D} ((s , hs) , eqs) = ∇ s (horiROrn-∇ {D = D s} (hs , eqs))

horiROrn :
  {I J : Set} {e : J → I} {D : RDesc I} {E : RDesc J} → HoriTrans e D E → ROrn e D E
horiROrn {E = ṿ js } (wrap f) = horiROrn-∇ (f tt)
horiROrn {E = σ S E} (wrap f) = Δ[ s ∶ S ] horiROrn {E = E s} (wrap (curry f s))

erase-horiROrn-∇ :
  {I J : Set} {e : J → I} (D : RDesc I) {js : List J}
  (hs : Hori D (const ⊤)) (eqs : Ė e js (Hori-indices D hs)) {X : I → Set} (xs : Ṁ (X ∘ e) js) →
  erase (horiROrn-∇ {D = D} (hs , eqs)) {X} xs ≡ Iso.from Fun (Hori-iso D (Ṁ X)) (hs , erase-Ṁ eqs xs)
erase-horiROrn-∇ (ṿ is)  hs       eqs xs = refl
erase-horiROrn-∇ (σ S D) (s , hs) eqs xs = cong₂-pair refl (≡-to-≅ (erase-horiROrn-∇ (D s) hs eqs xs))

erase-horiROrn :
  {I J : Set} {e : J → I} {D : RDesc I} {E : RDesc J} (f : HoriTrans e D E) {X : I → Set} (xs : ⟦ E ⟧ (X ∘ e)) →
  erase (horiROrn f) {X} xs ≡ HoriTrans-app f xs
erase-horiROrn {D = D} {ṿ js } (wrap f) xs       = uncurry (erase-horiROrn-∇ D) (f tt) xs
erase-horiROrn {D = D} {σ S E} (wrap f) (s , xs) = erase-horiROrn {D = D} {E s} (wrap (curry f s)) xs

horiROrn-id :
  {I : Set} {D : RDesc I} → ROrnEq (horiROrn (HoriTrans-id {I} {D})) (idROrn D)
horiROrn-id {I} {D} X xs xs' heq with HoriEq-to-≡ D xs xs' heq
horiROrn-id {I} {D} X xs ._  heq | refl =
  HoriEq-from-≡ D
    (begin
       erase (horiROrn (HoriTrans-id {I} {D})) xs
         ≡⟨ erase-horiROrn (HoriTrans-id {I} {D}) xs ⟩
       HoriTrans-app (HoriTrans-id {I} {D}) xs
         ≡⟨ cong (Hori-comp D (Ṁ X)) (cong (_,_ _) (erase-idROrn-Ṁ _ _)) ⟩
       Hori-comp D (Ṁ X) (Hori-decomp D (Ṁ X) xs)
         ≡⟨ Iso.from-to-inverse Fun (Hori-iso D (Ṁ X)) xs ⟩
       xs
         ≡⟨ sym (erase-idROrn D) ⟩
       erase (idROrn D) xs
     ∎)
  where open EqReasoning (≡-Setoid _)

horiROrn-comp :
  {I J K : Set} {e : J → I} {f : K → J} {D : RDesc I} {E : RDesc J} {F : RDesc K}
  (g : HoriTrans e D E) (h : HoriTrans f E F) → ROrnEq (horiROrn (HoriTrans-comp g h)) (scROrn (horiROrn g) (horiROrn h))
horiROrn-comp {e = e} {f} {D} {E} {F} g h X xs xs' heq with HoriEq-to-≡ F xs xs' heq
horiROrn-comp {e = e} {f} {D} {E} {F} g h X xs ._  heq | refl =
  HoriEq-from-≡ D
    (begin
       erase (horiROrn (HoriTrans-comp g h)) xs
         ≡⟨ erase-horiROrn (HoriTrans-comp g h) xs ⟩
       HoriTrans-app (HoriTrans-comp g h) xs
         ≡⟨ cong (Hori-comp D (Ṁ X)) (cong₂-pair (cong (proj₁ ∘ HoriTrans.comp g) (sym (cong proj₁ (Iso.to-from-inverse Fun (Hori-iso E (Ṁ (X ∘ e))) (proj₁ (HoriTrans.comp h (proj₁ (Hori-decomp F (Ṁ (λ x → X (e (f x)))) xs))) , erase-Ṁ (proj₂ (HoriTrans.comp h (proj₁ (Hori-decomp F (Ṁ (X ∘ e ∘ f)) xs)))) (proj₂ (Hori-decomp F (Ṁ (X ∘ e ∘ f)) xs))))))) {!(proj₂
 (HoriTrans.comp g
  (proj₁
   (Hori-decomp E (Ṁ (X ∘ e)) (HoriTrans-app h xs)))))
!}) ⟩
       HoriTrans-app g (HoriTrans-app h xs)
         ≡⟨ sym (erase-horiROrn g (HoriTrans-app h xs)) ⟩
       erase (horiROrn g) (HoriTrans-app h xs)
         ≡⟨ sym (cong (erase (horiROrn g)) (erase-horiROrn h xs)) ⟩
       erase (horiROrn g) (erase (horiROrn h) xs)
         ≡⟨ sym (erase-scROrn (horiROrn g) (horiROrn h) xs) ⟩

       erase (scROrn (horiROrn g) (horiROrn h)) xs
     ∎)
  where open EqReasoning (≡-Setoid _)
