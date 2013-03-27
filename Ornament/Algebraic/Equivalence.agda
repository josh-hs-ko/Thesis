-- Let `D : Desc I` be a description.
-- The category of relational `D`-algebras and the slice category of ornaments over `D` are equivalent.

module Thesis.Ornament.Algebraic.Equivalence where

open import Thesis.Prelude.Equality
open import Thesis.Prelude.Category.Isomorphism
open import Thesis.Prelude.Function
open import Thesis.Prelude.Function.Fam
open import Thesis.Prelude.Product
open import Thesis.Prelude.InverseImage
open import Thesis.Description
open import Thesis.Description.Horizontal
open import Thesis.Ornament
open import Thesis.Ornament.SequentialComposition
open import Thesis.Ornament.Horizontal
open import Thesis.Ornament.Equivalence
open import Thesis.Ornament.RefinementSemantics
open import Thesis.Ornament.Algebraic
open import Thesis.Relation
open import Thesis.Relation.Fold

open import Function using (id; const; _∘_)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_; curry; uncurry) renaming (map to _**_)
open import Data.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; cong; cong₂) renaming (setoid to ≡-Setoid)


--------
-- classifying algebras

mutual

  clsP : {I J : Set} {e : J → I} {D : RDesc I} {E : RDesc J} → ROrn e D E → ⟦ D ⟧ (InvImage e) → Set
  clsP (ṿ eqs)     js        = clsP-ṿ eqs js
  clsP (σ S O)     (s , js)  = clsP (O s) js
  clsP (Δ T O)     js        = Σ[ t ∶ T ] clsP (O t) js
  clsP (∇ s {D} O) (s' , js) = Σ (s ≡ s') (clsP-∇ {D = D} O js)

  clsP-ṿ : {I J : Set} {e : J → I} {js : List J} {is : List I} → Ė e js is → Ṁ (InvImage e) is → Set
  clsP-ṿ []              _         = ⊤
  clsP-ṿ (_∷_ {j} _ eqs) (j' , js) = und j' ≡ j × clsP-ṿ eqs js

  clsP-∇ : {I J : Set} {e : J → I} {S : Set} {D : S → RDesc I} {E : RDesc J} →
           {s : S} → ROrn e (D s) E → {s' : S} → ⟦ D s' ⟧ (InvImage e) → s ≡ s' → Set
  clsP-∇ O js refl = clsP O js

clsAlg : ∀ {I J} {e : J → I} {D E} (O : Orn e D E) → Ḟ D (InvImage e) ↝⁺ InvImage e
clsAlg O = wrap λ i js j → clsP (Orn.comp O j) js

-- algebraic ornamentation by a classifying algebra produces an isomorphic datatype

module AOCA {I J : Set} {e : J → I} {D : Desc I} {E : Desc J} (O : Orn e D E) where

  toAlgOrn-decomp :
    (D' : RDesc I) {i : I} (j : e ⁻¹ i) (R' : ⟦ D' ⟧ (InvImage e) ↝ InvImage e i) →
    (hs : Ṡ (toRDesc (algROrn D' j R'))) → Σ[ js ∶ ⟦ D' ⟧ (InvImage e) ] R' js j
  toAlgOrn-decomp (ṿ is)   j R' (js , r , _) = js , r
  toAlgOrn-decomp (σ S D') j R' (s , hs)     = (_,_ s ** id) (toAlgOrn-decomp (D' s) j (curry R' s) hs)

  toAlgOrn-Ė :
    {is : List I} {js : List J} (eqs : Ė e js is) (js' : Ṁ (InvImage e) is) → clsP-ṿ eqs js' →
    Ė (und ∘ proj₂) (und-Ṁ is (Ṁ-map (λ {i} j → ok (i , j)) is js')) js
  toAlgOrn-Ė [] _ _ = []
  toAlgOrn-Ė (_ ∷ eqs) (ok j , js') (eq , ps) = eq ∷ toAlgOrn-Ė eqs js' ps

  toAlgOrn-Ḣ :
    {D' : RDesc I} {E' : RDesc J} (O' : ROrn e D' E') →
    {i : I} (j : e ⁻¹ i) (R' : ⟦ D' ⟧ (InvImage e) ↝ InvImage e i) →
    (hs : Ṡ (toRDesc (algROrn D' j R'))) → clsP O' (proj₁ (toAlgOrn-decomp D' j R' hs)) →
    Σ[ hs' ∶ Ṡ E' ] Ė (und ∘ proj₂) (next (toRDesc (algROrn D' j R')) hs) (next E' hs')
  toAlgOrn-Ḣ (ṿ eqs)  j R' (js , r , hs) ps          = tt , toAlgOrn-Ė eqs js ps
  toAlgOrn-Ḣ (σ S O') j R' (s , hs)      ps          = (_,_ s ** id) (toAlgOrn-Ḣ (O' s) j (curry R' s) hs ps)
  toAlgOrn-Ḣ (Δ T O') j R' hs            (t , ps)    = (_,_ t ** id) (toAlgOrn-Ḣ (O' t) j R' hs ps)
  toAlgOrn-Ḣ (∇ s O') j R' (.s , hs)     (refl , ps) = toAlgOrn-Ḣ O' j (curry R' s) hs ps

  toAlgOrn-t : (i : I) (j : e ⁻¹ i) → ḢTrans (und ∘ proj₂) (Desc.comp E (und j)) (toRDesc (algROrn (Desc.comp D i) j ((clsAlg O !!) i)))
  toAlgOrn-t i j = let f = λ hs → toAlgOrn-Ḣ (Orn.comp O j) j ((clsAlg O !!) i) hs
                                    (proj₂ (toAlgOrn-decomp (Desc.comp D i) j ((clsAlg O !!) i) hs))
                   in  (proj₁ ∘ f , proj₂ ∘ f)

  toAlgOrn : Orn (und ∘ proj₂) E ⌊ algOrn D (clsAlg O) ⌋
  toAlgOrn = wrap λ { {._} (ok (i , j)) → ḢROrn (toAlgOrn-t i j) }

  fromAlgOrn-decomp-ṿ : {is : List I} {js : List J} (eqs : Ė e js is) → Σ (Ṁ (InvImage e) is) (clsP-ṿ eqs)
  fromAlgOrn-decomp-ṿ []           = tt , tt
  fromAlgOrn-decomp-ṿ (refl ∷ eqs) = (_,_ (ok _) ** _,_ refl) (fromAlgOrn-decomp-ṿ eqs)

  fromAlgOrn-decomp : {D' : RDesc I} {E' : RDesc J} (O' : ROrn e D' E') (hs : Ṡ E') → Σ (⟦ D' ⟧ (InvImage e)) (clsP O')
  fromAlgOrn-decomp (ṿ eqs)  _        = fromAlgOrn-decomp-ṿ eqs
  fromAlgOrn-decomp (σ S O') (s , hs) = (_,_ s ** id) (fromAlgOrn-decomp (O' s) hs)
  fromAlgOrn-decomp (Δ T O') (t , hs) = (id ** _,_ t) (fromAlgOrn-decomp (O' t) hs)
  fromAlgOrn-decomp (∇ s O') hs       = (_,_ s ** _,_ refl) (fromAlgOrn-decomp O' hs)

  fromAlgOrn-Ḣ-ṿ :
    {is : List I} {js : List J} (eqs : Ė e js is) →
    Ė {Σ I (InvImage e)} {J} (λ j → e j , ok j) js (und-Ṁ is (Ṁ-map (λ {i} j → ok (i , j)) is (proj₁ (fromAlgOrn-decomp-ṿ eqs))))
  fromAlgOrn-Ḣ-ṿ []           = []
  fromAlgOrn-Ḣ-ṿ (refl ∷ eqs) = refl ∷ fromAlgOrn-Ḣ-ṿ eqs

  fromAlgOrn-Ḣ :
    {D' : RDesc I} {E' : RDesc J} (O' : ROrn e D' E') →
    {i : I} (j : e ⁻¹ i) (R' : ⟦ D' ⟧ (InvImage e) ↝ InvImage e i) →
    (hs : Ṡ E') → R' (proj₁ (fromAlgOrn-decomp O' hs)) j →
    Σ[ hs' ∶ Ṡ (toRDesc (algROrn D' j R')) ] Ė (λ j → e j , ok j) (next E' hs) (next (toRDesc (algROrn D' j R')) hs')
  fromAlgOrn-Ḣ (ṿ eqs)  j R' _        r = (proj₁ (fromAlgOrn-decomp-ṿ eqs) , r , tt) , fromAlgOrn-Ḣ-ṿ eqs
  fromAlgOrn-Ḣ (σ S O') j R' (s , hs) r = (_,_ s ** id) (fromAlgOrn-Ḣ (O' s) j (curry R' s) hs r)
  fromAlgOrn-Ḣ (Δ T O') j R' (t , hs) r = fromAlgOrn-Ḣ (O' t) j R' hs r
  fromAlgOrn-Ḣ (∇ s O') j R' hs       r = (_,_ s ** id) (fromAlgOrn-Ḣ O' j (curry R' s) hs r)

  fromAlgOrn-t :
    (j : J) → ḢTrans (λ j → e j , ok j) (toRDesc (algROrn (Desc.comp D (e j)) (ok j) ((clsAlg O !!) (e j)))) (Desc.comp E j)
  fromAlgOrn-t j = let f = λ hs → fromAlgOrn-Ḣ (Orn.comp O (ok j)) (ok j) ((clsAlg O !!) (e j)) hs
                                    (proj₂ (fromAlgOrn-decomp (Orn.comp O (ok j)) hs))
                   in  (proj₁ ∘ f , proj₂ ∘ f)

  fromAlgOrn : Orn (λ j → e j , ok j) ⌊ algOrn D (clsAlg O) ⌋ E
  fromAlgOrn = wrap (λ { {._} (ok j) → ḢROrn (fromAlgOrn-t j) })

  toAlgOrn-fromAlgOrn-inverse : OrnEq (toAlgOrn ⊙ fromAlgOrn) (idOrn E)
  toAlgOrn-fromAlgOrn-inverse = frefl , (λ j → ROrnEq-trans frefl (Orn.comp (toAlgOrn ⊙ fromAlgOrn) (ok j)) (ḢROrn ḢTrans-id) (Orn.comp (idOrn E) (ok j)) (ROrnEq-trans frefl (Orn.comp (toAlgOrn ⊙ fromAlgOrn) (ok j)) (ḢROrn (ḢTrans-comp (toAlgOrn-t (e j) (ok j)) (fromAlgOrn-t j))) (ḢROrn ḢTrans-id) (ROrnEq-sym (ḢROrn (ḢTrans-comp (toAlgOrn-t (e j) (ok j)) (fromAlgOrn-t j))) (Orn.comp (toAlgOrn ⊙ fromAlgOrn) (ok j)) (ḢROrn-comp (toAlgOrn-t (e j) (ok j)) (fromAlgOrn-t j))) (ḢROrn-≐ (ḢTrans-comp (toAlgOrn-t (e j) (ok j)) (fromAlgOrn-t j)) ḢTrans-id {!!})) (ḢROrn-id {J} {Desc.comp E j}))

-- ḢROrn-≐ {!ḢTrans-comp (toAlgOrn-t (e j) (ok j)) (fromAlgOrn-t j)!} ḢTrans-id {!!}

{-

-- classifying algebra derived from an algebraic ornament is isomorphic to the algebra of the ornament

module CAAO {I : Set} {J : I → Set} (D : Desc I) (R : Ḟ D J ↝⁺ J) where

  h : J ⇉ _⁻¹_ proj₁
  h {i} = ok ∘ _,_ i

  CAAO-theorem-aux-computation : (D : RDesc I) (js : ⟦ D ⟧ J) → clsP (toROrn (erode D js)) (mapF D h js)
  CAAO-theorem-aux-computation ∎       js         = tt
  CAAO-theorem-aux-computation (ṿ i)   j          = refl
  CAAO-theorem-aux-computation (σ S D) (s , js)   = refl , CAAO-theorem-aux-computation (D s) js
  CAAO-theorem-aux-computation (D * E) (js , js') = CAAO-theorem-aux-computation D js , CAAO-theorem-aux-computation E js'

  CAAO-theorem-aux-unique : (D : RDesc I) (js js' : ⟦ D ⟧ J) → clsP (toROrn (erode D js')) (mapF D h js) → js ≡ js'
  CAAO-theorem-aux-unique ∎       js        js'         p          = refl
  CAAO-theorem-aux-unique (ṿ i)   j         j'          p          = cong-proj₂ p
  CAAO-theorem-aux-unique (σ S D) (s , js)  (.s , js')  (refl , p) = cong (_,_ s) (CAAO-theorem-aux-unique (D s) js js' p)
  CAAO-theorem-aux-unique (D * E) (js , ks) (js' , ks') (p , p')   = cong₂ _,_ (CAAO-theorem-aux-unique D js js' p)
                                                                               (CAAO-theorem-aux-unique E ks ks' p')

  CAAO-theorem : fun⁺ h •⁺ R ≃⁺ clsAlg ⌈ algOrn D R ⌉ •⁺ Ṙ D (fun⁺ h)
  CAAO-theorem =
    wrap (λ i → wrap λ { js ._ (j , r , refl) →
                         Ḟ-map D h js , mapR-fun-computation (D at i) h js , js , r , CAAO-theorem-aux-computation (D at i) js }) ,
    wrap (λ i → wrap λ { js ij (ijs , rs , q) → aux js ij ijs rs q })
    where
      aux : ∀ {i} (js : Ḟ D J i) (ij : proj₁ {B = J} ⁻¹ i) (ijs : Ḟ D (_⁻¹_ proj₁) i) (rs : mapR (D at i) (fun⁺ h) js ijs) →
            (q : (clsAlg ⌈ algOrn D R ⌉ !!) i ijs ij) → ((fun⁺ h •⁺ R) !!) i js ij
      aux js (ok (i , j)) ijs rs (js' , r , p) with mapR-fun-unique (D at i) h js ijs rs
      aux js (ok (i , j)) ._  rs (js' , r , p) | refl with CAAO-theorem-aux-unique (D at i) js js' p
      aux js (ok (i , j)) ._  rs (.js , r , p) | refl | refl = j , r , refl

  g : _⁻¹_ proj₁ ⇉ J
  g (ok (i , j)) = j

  hg-inverse : ∀ {i} (ij : proj₁ ⁻¹ i) → h (g ij) ≡ ij
  hg-inverse (ok (i , j)) = refl

  hg-iso : ∀ i → Iso Fun (J i) (proj₁ {B = J} ⁻¹ i)
  hg-iso i = record { to = h; from = g; to-from-inverse = hg-inverse; from-to-inverse = frefl }

-}
