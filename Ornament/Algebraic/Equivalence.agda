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
open import Data.List using (List; []; _∷_; map)
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

  toAlgOrn-decomp : (D' : RDesc I) (P : ℘ (⟦ D' ⟧ (InvImage e))) (hs : Ṡ (toRDesc (algROrn D' P))) → Σ (⟦ D' ⟧ (InvImage e)) P
  toAlgOrn-decomp (ṿ is)   P (js , p , _) = js , p
  toAlgOrn-decomp (σ S D') P (s , hs)     = (_,_ s ** id) (toAlgOrn-decomp (D' s) (curry P s) hs)

  toAlgOrn-comp : {D' : RDesc I} {E' : RDesc J} (O' : ROrn e D' E') (js : ⟦ D' ⟧ (InvImage e)) → clsP O' js → Ṡ E'
  toAlgOrn-comp (ṿ eqs)  js        ps          = tt
  toAlgOrn-comp (σ S O') (s , js)  ps          = s , toAlgOrn-comp (O' s) js ps
  toAlgOrn-comp (Δ T O') js        (t , ps)    = t , toAlgOrn-comp (O' t) js ps
  toAlgOrn-comp (∇ s O') (.s , js) (refl , ps) = toAlgOrn-comp O' js ps

  toAlgOrn-Ė :
    {is : List I} {js : List J} (eqs : Ė e js is) (js' : Ṁ (InvImage e) is) → clsP-ṿ eqs js' →
    Ė (und ∘ proj₂) (und-Ṁ is (Ṁ-map (λ {i} j → ok (i , j)) is js')) js
  toAlgOrn-Ė []        _            _         = []
  toAlgOrn-Ė (_ ∷ eqs) (ok j , js') (eq , ps) = eq ∷ toAlgOrn-Ė eqs js' ps

  toAlgOrn-c :
    {D' : RDesc I} {E' : RDesc J} (O' : ROrn e D' E') (P : ℘ (⟦ D' ⟧ (InvImage e)))
    (hs : Ṡ (toRDesc (algROrn D' P))) (ps : clsP O' (proj₁ (toAlgOrn-decomp D' P hs))) →
    Ė (und ∘ proj₂) (next (toRDesc (algROrn D' P)) hs) (next E' (toAlgOrn-comp O' (proj₁ (toAlgOrn-decomp D' P hs)) ps))
  toAlgOrn-c (ṿ eqs)  P (js , p , _) ps          = toAlgOrn-Ė eqs js ps
  toAlgOrn-c (σ S O') P (s , hs)     ps          = toAlgOrn-c (O' s) (curry P s) hs ps
  toAlgOrn-c (Δ T O') P hs           (t , ps)    = toAlgOrn-c (O' t) P hs ps
  toAlgOrn-c (∇ s O') P (.s , hs)    (refl , ps) = toAlgOrn-c O' (curry P s) hs ps

  toAlgOrn-t : (i : I) (j : e ⁻¹ i) → ḢTrans (und ∘ proj₂) (Desc.comp E (und j)) (toRDesc (algROrn (Desc.comp D i) (((clsAlg O !!) i º) j)))
  toAlgOrn-t i j =
    uncurry (toAlgOrn-comp (Orn.comp O j)) ∘ toAlgOrn-decomp (Desc.comp D i) (((clsAlg O !!) i º) j) ,
    λ hs → toAlgOrn-c (Orn.comp O j) (((clsAlg O !!) i º) j) hs (proj₂ (toAlgOrn-decomp (Desc.comp D i) (((clsAlg O !!) i º) j) hs))

  toAlgOrn : Orn (und ∘ proj₂) E ⌊ algOrn D (clsAlg O) ⌋
  toAlgOrn = wrap λ { {._} (ok (i , j)) → ḢROrn (toAlgOrn-t i j) }

  fromAlgOrn-comp : (D' : RDesc I) (P : ℘ (⟦ D' ⟧ (InvImage e))) (js : ⟦ D' ⟧ (InvImage e)) → P js → Ṡ (toRDesc (algROrn D' P))
  fromAlgOrn-comp (ṿ is)   P js       p = js , p , tt
  fromAlgOrn-comp (σ S D') P (s , js) p = s , fromAlgOrn-comp (D' s) (curry P s) js p

  fromAlgOrn-decomp-ṿ : {is : List I} {js : List J} (eqs : Ė e js is) → Σ (Ṁ (InvImage e) is) (clsP-ṿ eqs)
  fromAlgOrn-decomp-ṿ []           = tt , tt
  fromAlgOrn-decomp-ṿ (refl ∷ eqs) = (_,_ (ok _) ** _,_ refl) (fromAlgOrn-decomp-ṿ eqs)

  fromAlgOrn-decomp : {D' : RDesc I} {E' : RDesc J} (O' : ROrn e D' E') (hs : Ṡ E') → Σ (⟦ D' ⟧ (InvImage e)) (clsP O')
  fromAlgOrn-decomp (ṿ eqs)  _        = fromAlgOrn-decomp-ṿ eqs
  fromAlgOrn-decomp (σ S O') (s , hs) = (_,_ s ** id) (fromAlgOrn-decomp (O' s) hs)
  fromAlgOrn-decomp (Δ T O') (t , hs) = (id ** _,_ t) (fromAlgOrn-decomp (O' t) hs)
  fromAlgOrn-decomp (∇ s O') hs       = (_,_ s ** _,_ refl) (fromAlgOrn-decomp O' hs)

  fromAlgOrn-c-ṿ :
    {is : List I} {js : List J} (eqs : Ė e js is) →
    Ė {Σ I (InvImage e)} {J} (λ j → e j , ok j) js (und-Ṁ is (Ṁ-map (λ {i} j → ok (i , j)) is (proj₁ (fromAlgOrn-decomp-ṿ eqs))))
  fromAlgOrn-c-ṿ []           = []
  fromAlgOrn-c-ṿ (refl ∷ eqs) = refl ∷ fromAlgOrn-c-ṿ eqs

  fromAlgOrn-c :
    {D' : RDesc I} {E' : RDesc J} (O' : ROrn e D' E') (P : ℘ (⟦ D' ⟧ (InvImage e))) (hs : Ṡ E') (p : P (proj₁ (fromAlgOrn-decomp O' hs))) →
    Ė (λ j → e j , ok j) (next E' hs) (next (toRDesc (algROrn D' P)) (fromAlgOrn-comp D' P (proj₁ (fromAlgOrn-decomp O' hs)) p))
  fromAlgOrn-c (ṿ eqs)  P hs       p = fromAlgOrn-c-ṿ eqs
  fromAlgOrn-c (σ S O') P (s , hs) p = fromAlgOrn-c (O' s) (curry P s) hs p
  fromAlgOrn-c (Δ T O') P (t , hs) p = fromAlgOrn-c (O' t) P hs p
  fromAlgOrn-c (∇ s O') P hs       p = fromAlgOrn-c O' (curry P s) hs p

  fromAlgOrn-t : (j : J) → ḢTrans (λ j → e j , ok j) (toRDesc (algROrn (Desc.comp D (e j)) (((clsAlg O !!) (e j) º) (ok j)))) (Desc.comp E j)
  fromAlgOrn-t j =
    uncurry (fromAlgOrn-comp (Desc.comp D (e j)) (((clsAlg O !!) (e j) º) (ok j))) ∘ fromAlgOrn-decomp (Orn.comp O (ok j)) ,
    λ hs → fromAlgOrn-c (Orn.comp O (ok j)) (((clsAlg O !!) (e j) º) (ok j)) hs (proj₂ (fromAlgOrn-decomp (Orn.comp O (ok j)) hs))

  fromAlgOrn : Orn (λ j → e j , ok j) ⌊ algOrn D (clsAlg O) ⌋ E
  fromAlgOrn = wrap (λ { {._} (ok j) → ḢROrn (fromAlgOrn-t j) })

  toAlgOrn-decomp-fromAlgOrn-comp-inverse :
    (D' : RDesc I) (P : ℘ (⟦ D' ⟧ (InvImage e))) → toAlgOrn-decomp D' P ∘ uncurry (fromAlgOrn-comp D' P) ≐ id
  toAlgOrn-decomp-fromAlgOrn-comp-inverse (ṿ is)   P (js , ps)       = refl
  toAlgOrn-decomp-fromAlgOrn-comp-inverse (σ S D') P ((s , js) , ps) = cong (_,_ s ** id)
                                                                            (toAlgOrn-decomp-fromAlgOrn-comp-inverse (D' s) (curry P s) (js , ps))

  toAlgOrn-comp-fromAlgOrn-decomp-inverse :
    {D' : RDesc I} {E' : RDesc J} (O' : ROrn e D' E') → uncurry (toAlgOrn-comp O') ∘ fromAlgOrn-decomp O' ≐ id
  toAlgOrn-comp-fromAlgOrn-decomp-inverse (ṿ eqs)  _        = refl
  toAlgOrn-comp-fromAlgOrn-decomp-inverse (σ S O') (s , hs) = cong (_,_ s) (toAlgOrn-comp-fromAlgOrn-decomp-inverse (O' s) hs)
  toAlgOrn-comp-fromAlgOrn-decomp-inverse (Δ T O') (t , hs) = cong (_,_ t) (toAlgOrn-comp-fromAlgOrn-decomp-inverse (O' t) hs)
  toAlgOrn-comp-fromAlgOrn-decomp-inverse (∇ s O') hs       = toAlgOrn-comp-fromAlgOrn-decomp-inverse O' hs

  toAlgOrn-fromAlgOrn-inverse : OrnEq (toAlgOrn ⊙ fromAlgOrn) (idOrn E)
  toAlgOrn-fromAlgOrn-inverse =
    frefl ,
    (λ j → ROrnEq-trans frefl
             (Orn.comp (toAlgOrn ⊙ fromAlgOrn) (ok j)) (ḢROrn ḢTrans-id) (Orn.comp (idOrn E) (ok j))
             (ROrnEq-trans frefl
                (Orn.comp (toAlgOrn ⊙ fromAlgOrn) (ok j)) (ḢROrn (ḢTrans-comp (toAlgOrn-t (e j) (ok j)) (fromAlgOrn-t j))) (ḢROrn ḢTrans-id)
                (ROrnEq-sym (ḢROrn (ḢTrans-comp (toAlgOrn-t (e j) (ok j)) (fromAlgOrn-t j))) (Orn.comp (toAlgOrn ⊙ fromAlgOrn) (ok j))
                   (ḢROrn-comp (toAlgOrn-t (e j) (ok j)) (fromAlgOrn-t j)))
                (ḢROrn-≐ (ḢTrans-comp (toAlgOrn-t (e j) (ok j)) (fromAlgOrn-t j)) ḢTrans-id
                         (ftrans (fcong-l (uncurry (toAlgOrn-comp (Orn.comp O (ok j))))
                                    (fcong-r (fromAlgOrn-decomp (Orn.comp O (ok j)))
                                       (toAlgOrn-decomp-fromAlgOrn-comp-inverse (Desc.comp D (e j)) (((clsAlg O !!) (e j) º) (ok j)))))
                                 (toAlgOrn-comp-fromAlgOrn-decomp-inverse (Orn.comp O (ok j))))))
             (ḢROrn-id {J} {Desc.comp E j}))

  fromAlgOrn-decomp-ṿ-unique :
    {is : List I} {js : List J} (eqs : Ė e js is) (js : Ṁ (InvImage e) is) (ps : clsP-ṿ eqs js) → fromAlgOrn-decomp-ṿ eqs ≡ (js , ps)
  fromAlgOrn-decomp-ṿ-unique []         _           _                   = refl
  fromAlgOrn-decomp-ṿ-unique (eq ∷ eqs) (ok j , js) (refl , ps) with eq
  fromAlgOrn-decomp-ṿ-unique (eq ∷ eqs) (ok j , js) (refl , ps) | refl  = cong (_,_ (ok j) ** _,_ refl) (fromAlgOrn-decomp-ṿ-unique eqs js ps)

  fromAlgOrn-decomp-toAlgOrn-comp-inverse :
    {D' : RDesc I} {E' : RDesc J} (O' : ROrn e D' E') → fromAlgOrn-decomp O' ∘ uncurry (toAlgOrn-comp O') ≐ id
  fromAlgOrn-decomp-toAlgOrn-comp-inverse (ṿ eqs)  (js        , ps         ) = fromAlgOrn-decomp-ṿ-unique eqs js ps
  fromAlgOrn-decomp-toAlgOrn-comp-inverse (σ S O') ((s , js)  , ps         ) = cong (_,_ s ** id)
                                                                                    (fromAlgOrn-decomp-toAlgOrn-comp-inverse (O' s) (js , ps))
  fromAlgOrn-decomp-toAlgOrn-comp-inverse (Δ T O') (js        , (t , ps)   ) = cong (id ** _,_ t)
                                                                                    (fromAlgOrn-decomp-toAlgOrn-comp-inverse (O' t) (js , ps))
  fromAlgOrn-decomp-toAlgOrn-comp-inverse (∇ s O') ((.s , js) , (refl , ps)) = cong (_,_ s ** _,_ refl)
                                                                                    (fromAlgOrn-decomp-toAlgOrn-comp-inverse O' (js , ps))

  fromAlgOrn-comp-toAlgOrn-decomp-inverse :
    (D' : RDesc I) (P : ℘ (⟦ D' ⟧ (InvImage e))) → uncurry (fromAlgOrn-comp D' P) ∘ toAlgOrn-decomp D' P ≐ id
  fromAlgOrn-comp-toAlgOrn-decomp-inverse (ṿ is)   P (js , p , _) = refl
  fromAlgOrn-comp-toAlgOrn-decomp-inverse (σ S D') P (s , hs)     = cong (_,_ s) (fromAlgOrn-comp-toAlgOrn-decomp-inverse (D' s) (curry P s) hs)

  fromAlgOrn-toAlgOrn-inverse : OrnEq (fromAlgOrn ⊙ toAlgOrn) (idOrn ⌊ algOrn D (clsAlg O) ⌋)
  fromAlgOrn-toAlgOrn-inverse =
    (λ { (._ , ok j) → refl }) ,
    (λ { (._ , ok j) → {!!} })
{-
           ROrnEq-trans {!!}
             (Orn.comp (fromAlgOrn ⊙ toAlgOrn) (ok (e j , ok j))) {!(Orn.comp (fromAlgOrn ⊙ toAlgOrn) (ok (e j , ok j)))!} (Orn.comp (idOrn ⌊ algOrn D (clsAlg O) ⌋) (ok (e j , ok j)))
             {!ROrnEq-trans frefl
                (Orn.comp (fromAlgOrn ⊙ toAlgOrn) (ok (e j , ok j))) (ḢROrn (ḢTrans-comp (fromAlgOrn-t j) (toAlgOrn-t (e j) (ok j)))) (ḢROrn ḢTrans-id)
                (ROrnEq-sym (ḢROrn (ḢTrans-comp (fromAlgOrn-t j) (toAlgOrn-t (e j) (ok j)))) (Orn.comp (fromAlgOrn ⊙ toAlgOrn) (ok (e j , ok j)))
                   (ḢROrn-comp (fromAlgOrn-t j) (toAlgOrn-t (e j) (ok j))))
                (ḢROrn-≐ (ḢTrans-comp (fromAlgOrn-t j) (toAlgOrn-t (e j) (ok j))) ḢTrans-id
                         {!ftrans (fcong-l (uncurry (toAlgOrn-comp (Orn.comp O (ok j))))
                                    (fcong-r (fromAlgOrn-decomp (Orn.comp O (ok j)))
                                       (toAlgOrn-decomp-fromAlgOrn-comp-inverse (Desc.comp D (e j)) (((clsAlg O !!) (e j) º) (ok j)))))
                                 (toAlgOrn-comp-fromAlgOrn-decomp-inverse (Orn.comp O (ok j)))!})!}
             {!ḢROrn-id {_} {Desc.comp ⌊ algOrn D (clsAlg O) ⌋ (e j , ok j)}!} })

-- classifying algebra derived from an algebraic ornament is isomorphic to the algebra of the ornament

module CAAO {I : Set} {J : I → Set} (D : Desc I) (R : Ḟ D J ↝⁺ J) where

  h : J ⇉ InvImage proj₁
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

  g : InvImage proj₁ ⇉ J
  g (ok (i , j)) = j

  hg-inverse : ∀ {i} (ij : proj₁ ⁻¹ i) → h (g ij) ≡ ij
  hg-inverse (ok (i , j)) = refl

  hg-iso : ∀ i → Iso Fun (J i) (proj₁ {B = J} ⁻¹ i)
  hg-iso i = record { to = h; from = g; to-from-inverse = hg-inverse; from-to-inverse = frefl }

-}
