-- Let `D : Desc I` be a description.
-- The category of relational `D`-algebras and the slice category of ornaments over `D` are equivalent.

module Thesis.Ornament.Algebraic.Equivalence where

open import Thesis.Prelude.Equality
open import Thesis.Prelude.Category.Isomorphism
open import Thesis.Prelude.Preorder
open import Thesis.Prelude.Function
open import Thesis.Prelude.Function.Fam
open import Thesis.Prelude.Product
open import Thesis.Prelude.InverseImage
open import Thesis.Description
open import Thesis.Description.Horizontal
open import Thesis.Description.HorizontalEquivalence
open import Thesis.Ornament
open import Thesis.Ornament.SequentialComposition
open import Thesis.Ornament.Horizontal
open import Thesis.Ornament.Equivalence
open import Thesis.Ornament.RefinementSemantics
open import Thesis.Ornament.Algebraic
open import Thesis.Relation
open import Thesis.Relation.CompChain
open import Thesis.Relation.Fold

open import Function using (id; const; flip; _∘_)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_; curry; uncurry) renaming (map to _**_)
open import Data.List using (List; []; _∷_; map)
open import Relation.Binary using (module Setoid)
import Relation.Binary.PreorderReasoning as PreorderReasoning
import Relation.Binary.EqReasoning as EqReasoning
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


{-------
-- algebraic ornamentation by a classifying algebra produces an isomorphic datatype

module AOCA {I J : Set} {e : J → I} {D : Desc I} {E : Desc J} (O : Orn e D E) where

  g : Σ I (InvImage e) → J
  g = und ∘ proj₂

  h : J → Σ I (InvImage e)
  h j = e j , ok j

  gh-inverse : g ∘ h ≐ id
  gh-inverse = frefl

  hg-inverse : h ∘ g ≐ id
  hg-inverse (._ , ok j) = refl

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
    Ė g (und-Ṁ is (Ṁ-map (λ {i} j → ok (i , j)) is js')) js
  toAlgOrn-Ė []        _            _         = []
  toAlgOrn-Ė (_ ∷ eqs) (ok j , js') (eq , ps) = eq ∷ toAlgOrn-Ė eqs js' ps

  toAlgOrn-c :
    {D' : RDesc I} {E' : RDesc J} (O' : ROrn e D' E') (P : ℘ (⟦ D' ⟧ (InvImage e)))
    (hs : Ṡ (toRDesc (algROrn D' P))) (ps : clsP O' (proj₁ (toAlgOrn-decomp D' P hs))) →
    Ė g (next (toRDesc (algROrn D' P)) hs) (next E' (toAlgOrn-comp O' (proj₁ (toAlgOrn-decomp D' P hs)) ps))
  toAlgOrn-c (ṿ eqs)  P (js , p , _) ps          = toAlgOrn-Ė eqs js ps
  toAlgOrn-c (σ S O') P (s , hs)     ps          = toAlgOrn-c (O' s) (curry P s) hs ps
  toAlgOrn-c (Δ T O') P hs           (t , ps)    = toAlgOrn-c (O' t) P hs ps
  toAlgOrn-c (∇ s O') P (.s , hs)    (refl , ps) = toAlgOrn-c O' (curry P s) hs ps

  toAlgOrn-t : (i : I) (j : e ⁻¹ i) → ḢTrans g (Desc.comp E (und j)) (toRDesc (algROrn (Desc.comp D i) (((clsAlg O !!) i º) j)))
  toAlgOrn-t i j =
    uncurry (toAlgOrn-comp (Orn.comp O j)) ∘ toAlgOrn-decomp (Desc.comp D i) (((clsAlg O !!) i º) j) ,
    λ hs → toAlgOrn-c (Orn.comp O j) (((clsAlg O !!) i º) j) hs (proj₂ (toAlgOrn-decomp (Desc.comp D i) (((clsAlg O !!) i º) j) hs))

  toAlgOrn : Orn g E ⌊ algOrn D (clsAlg O) ⌋
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
    Ė h js (und-Ṁ is (Ṁ-map (λ {i} j → ok (i , j)) is (proj₁ (fromAlgOrn-decomp-ṿ eqs))))
  fromAlgOrn-c-ṿ []           = []
  fromAlgOrn-c-ṿ (refl ∷ eqs) = refl ∷ fromAlgOrn-c-ṿ eqs

  fromAlgOrn-c :
    {D' : RDesc I} {E' : RDesc J} (O' : ROrn e D' E') (P : ℘ (⟦ D' ⟧ (InvImage e))) (hs : Ṡ E') (p : P (proj₁ (fromAlgOrn-decomp O' hs))) →
    Ė h (next E' hs) (next (toRDesc (algROrn D' P)) (fromAlgOrn-comp D' P (proj₁ (fromAlgOrn-decomp O' hs)) p))
  fromAlgOrn-c (ṿ eqs)  P hs       p = fromAlgOrn-c-ṿ eqs
  fromAlgOrn-c (σ S O') P (s , hs) p = fromAlgOrn-c (O' s) (curry P s) hs p
  fromAlgOrn-c (Δ T O') P (t , hs) p = fromAlgOrn-c (O' t) P hs p
  fromAlgOrn-c (∇ s O') P hs       p = fromAlgOrn-c O' (curry P s) hs p

  fromAlgOrn-t : (j : J) → ḢTrans h (toRDesc (algROrn (Desc.comp D (e j)) (((clsAlg O !!) (e j) º) (ok j)))) (Desc.comp E j)
  fromAlgOrn-t j =
    uncurry (fromAlgOrn-comp (Desc.comp D (e j)) (((clsAlg O !!) (e j) º) (ok j))) ∘ fromAlgOrn-decomp (Orn.comp O (ok j)) ,
    λ hs → fromAlgOrn-c (Orn.comp O (ok j)) (((clsAlg O !!) (e j) º) (ok j)) hs (proj₂ (fromAlgOrn-decomp (Orn.comp O (ok j)) hs))

  fromAlgOrn : Orn h ⌊ algOrn D (clsAlg O) ⌋ E
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
    gh-inverse ,
    (λ j → ROrnEq-trans frefl
             (Orn.comp (toAlgOrn ⊙ fromAlgOrn) (ok j)) (ḢROrn ḢTrans-id) (Orn.comp (idOrn E) (ok j))
             (ROrnEq-trans frefl
                (Orn.comp (toAlgOrn ⊙ fromAlgOrn) (ok j)) (ḢROrn (ḢTrans-comp (toAlgOrn-t (e j) (ok j)) (fromAlgOrn-t j))) (ḢROrn ḢTrans-id)
                (ROrnEq-sym (ḢROrn (ḢTrans-comp (toAlgOrn-t (e j) (ok j)) (fromAlgOrn-t j))) (Orn.comp (toAlgOrn ⊙ fromAlgOrn) (ok j))
                   (ḢROrn-comp (toAlgOrn-t (e j) (ok j)) (fromAlgOrn-t j)))
                (ḢROrn-≐ (ḢTrans-comp (toAlgOrn-t (e j) (ok j)) (fromAlgOrn-t j)) ḢTrans-id gh-inverse
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
    hg-inverse ,
    (λ { (._ , ok j) →
         ROrnEq-trans hg-inverse
           (Orn.comp (fromAlgOrn ⊙ toAlgOrn) (ok (e j , ok j))) (ḢROrn ḢTrans-id) ((Orn.comp (idOrn ⌊ algOrn D (clsAlg O) ⌋) (ok (e j , ok j))))
           (ROrnEq-trans frefl
              (Orn.comp (fromAlgOrn ⊙ toAlgOrn) (ok (e j , ok j))) (ḢROrn (ḢTrans-comp (fromAlgOrn-t j) (toAlgOrn-t (e j) (ok j)))) (ḢROrn ḢTrans-id)
              (ROrnEq-sym (ḢROrn (ḢTrans-comp (fromAlgOrn-t j) (toAlgOrn-t (e j) (ok j)))) (Orn.comp (fromAlgOrn ⊙ toAlgOrn) (ok (e j , ok j)))
                 (ḢROrn-comp (fromAlgOrn-t j) (toAlgOrn-t (e j) (ok j))))
              (ḢROrn-≐ (ḢTrans-comp (fromAlgOrn-t j) (toAlgOrn-t (e j) (ok j))) ḢTrans-id hg-inverse
                 (ftrans (fcong-l (uncurry (fromAlgOrn-comp (Desc.comp D (e j)) (((clsAlg O !!) (e j) º) (ok j))))
                            (fcong-r (toAlgOrn-decomp (Desc.comp D (e j)) (((clsAlg O !!) (e j) º) (ok j)))
                               (fromAlgOrn-decomp-toAlgOrn-comp-inverse (Orn.comp O (ok j)))))
                         (fromAlgOrn-comp-toAlgOrn-decomp-inverse (Desc.comp D (e j)) (((clsAlg O !!) (e j) º) (ok j))))))
           (ḢROrn-id {Σ I (InvImage e)} {Desc.comp ⌊ algOrn D (clsAlg O) ⌋ (e j , ok j)}) })

-}


--------
-- classifying algebra derived from an algebraic ornament is isomorphic to the algebra of the ornament

module CAAO {I : Set} {J : I → Set} (D : Desc I) (R : Ḟ D J ↝⁺ J) where

  g : J ⇉ InvImage proj₁
  g {i} = ok ∘ _,_ i

  h : InvImage proj₁ ⇉ J
  h (ok (i , j)) = j

  gh-inverse : ∀ {i} (ij : proj₁ ⁻¹ i) → g (h ij) ≡ ij
  gh-inverse (ok (i , j)) = refl

  hg-inverse : ∀ {i} (j : J i) → h (g j) ≡ j
  hg-inverse = frefl

  gh-iso : ∀ i → Iso Fun (J i) (proj₁ {B = J} ⁻¹ i)
  gh-iso i = record { to = g; from = h; to-from-inverse = gh-inverse; from-to-inverse = hg-inverse }

  CAAO-computation-ṿ : (is : List I) (js : Ṁ J is) → clsP-ṿ (to≡-Ṁ is (Ṁ-map g is js)) (Ṁ-map g is js)
  CAAO-computation-ṿ []       _        = tt
  CAAO-computation-ṿ (i ∷ is) (j , js) = refl , CAAO-computation-ṿ is js

  CAAO-computation : (D' : RDesc I) (P : ℘ (⟦ D' ⟧ J)) (js : ⟦ D' ⟧ J) → P js → clsP (toROrn (algROrn D' P)) (mapF D' g js)
  CAAO-computation (ṿ is)   P js       p = js , p , CAAO-computation-ṿ is js
  CAAO-computation (σ S D') P (s , js) p = CAAO-computation (D' s) (curry P s) js p

  CAAO-extraction-ṿ : (is : List I) (js js' : Ṁ J is) → clsP-ṿ (to≡-Ṁ is (Ṁ-map g is js')) (Ṁ-map g is js) → js ≡ js'
  CAAO-extraction-ṿ []       _        _          _            = refl
  CAAO-extraction-ṿ (i ∷ is) (j , js) (.j , js') (refl , eqs) = cong (_,_ j) (CAAO-extraction-ṿ is js js' eqs)

  CAAO-extraction : (D' : RDesc I) (P : ℘ (⟦ D' ⟧ J)) (js : ⟦ D' ⟧ J) → clsP (toROrn (algROrn D' P)) (mapF D' g js) → P js
  CAAO-extraction (ṿ is)   P js       (js' , p , eqs) with CAAO-extraction-ṿ is js js' eqs
  CAAO-extraction (ṿ is)   P js       (.js , p , eqs) | refl = p
  CAAO-extraction (σ S D') P (s , js) p                      = CAAO-extraction (D' s) (curry P s) js p

  R-to-clsAlg : fun⁺ g •⁺ R ≃⁺ clsAlg ⌈ algOrn D R ⌉ •⁺ Ṙ D (fun⁺ g)
  R-to-clsAlg = wrap (λ i → wrap λ { js ._ (j , r , refl) →
                                       Ḟ-map D g js ,
                                       mapR-fun-computation (Desc.comp D i) g js ,
                                       CAAO-computation (Desc.comp D i) (((R !!) i º) j) js r }) ,
                wrap (λ i → wrap λ { js ij (ijs , rs , q) → aux js ij ijs rs q })
    where
      aux : ∀ {i} (js : Ḟ D J i) (ij : proj₁ {B = J} ⁻¹ i) (ijs : Ḟ D (_⁻¹_ proj₁) i) (rs : mapR (Desc.comp D i) (fun⁺ g) js ijs) →
            (q : (clsAlg ⌈ algOrn D R ⌉ !!) i ijs ij) → ((fun⁺ g •⁺ R) !!) i js ij
      aux js (ok (i , j)) ijs rs p with mapR-fun-unique (Desc.comp D i) g js ijs rs
      aux js (ok (i , j)) ._  rs p | refl = j , CAAO-extraction (Desc.comp D i) (((R !!) i º) j) js p , refl

  clsAlg-to-R : fun⁺ h •⁺ clsAlg ⌈ algOrn D R ⌉ ≃⁺ R •⁺ Ṙ D (fun⁺ h)
  clsAlg-to-R =
    (begin
       fun⁺ g •⁺ R ≃⁺ clsAlg ⌈ algOrn D R ⌉ •⁺ Ṙ D (fun⁺ g)
         ⇒⟨ •⁺-cong-l (fun⁺ h) ⟩
       fun⁺ h •⁺ fun⁺ g •⁺ R ≃⁺ fun⁺ h •⁺ clsAlg ⌈ algOrn D R ⌉ •⁺ Ṙ D (fun⁺ g)
         ⇒⟨ ≃⁺-trans (≃⁺-chain (fun⁺ h ◇⁺) (fun⁺ h º⁺ ◇⁺) (fun⁺ g ◇⁺) (iso⁺-conv (Setoid.sym (IsoSetoid Fun) ∘ gh-iso))) ⟩
       fun⁺ h •⁺ fun⁺ h º⁺ •⁺ R ≃⁺ fun⁺ h •⁺ clsAlg ⌈ algOrn D R ⌉ •⁺ Ṙ D (fun⁺ g)
         ⇒⟨ ≃⁺-trans (≃⁺-sym (≃⁺-chain-r (fun⁺ h ▪⁺ fun⁺ h º⁺ ◇⁺) (idR⁺ ◇⁺) (iso⁺-idR⁺ (Setoid.sym (IsoSetoid Fun) ∘ gh-iso)))) ⟩
       idR⁺ •⁺ R ≃⁺ fun⁺ h •⁺ clsAlg ⌈ algOrn D R ⌉ •⁺ Ṙ D (fun⁺ g)
         ⇒⟨ ≃⁺-trans (≃⁺-sym (idR⁺-l R)) ⟩
       R ≃⁺ fun⁺ h •⁺ clsAlg ⌈ algOrn D R ⌉ •⁺ Ṙ D (fun⁺ g)
         ⇒⟨ •⁺-cong-r (Ṙ D (fun⁺ h)) ⟩
       R •⁺ Ṙ D (fun⁺ h) ≃⁺ (fun⁺ h •⁺ clsAlg ⌈ algOrn D R ⌉ •⁺ Ṙ D (fun⁺ g)) •⁺ Ṙ D (fun⁺ h)
         ⇒⟨ flip ≃⁺-trans
              (begin′
                 (fun⁺ h •⁺ clsAlg ⌈ algOrn D R ⌉ •⁺ Ṙ D (fun⁺ g)) •⁺ Ṙ D (fun⁺ h)
                   ≃⁺⟨ ≃⁺-sym (•⁺-cong-l (fun⁺ h •⁺ clsAlg ⌈ algOrn D R ⌉ •⁺ Ṙ D (fun⁺ g)) (Ṙ-cong D (iso⁺-conv gh-iso))) ⟩
                 (fun⁺ h •⁺ clsAlg ⌈ algOrn D R ⌉ •⁺ Ṙ D (fun⁺ g)) •⁺ Ṙ D (fun⁺ g º⁺)
                   ≃⁺⟨ chain-normalise⁺ (([ fun⁺ h ]⁺ ▪⁺ [ clsAlg ⌈ algOrn D R ⌉ ]⁺ ▪⁺ [ Ṙ D (fun⁺ g) ]⁺) ▪⁺ [ Ṙ D (fun⁺ g º⁺) ]⁺) ⟩
                 fun⁺ h •⁺ clsAlg ⌈ algOrn D R ⌉ •⁺ Ṙ D (fun⁺ g) •⁺ Ṙ D (fun⁺ g º⁺)
                   ≃⁺⟨ ≃⁺-sym (≃⁺-chain-l (fun⁺ h ▪⁺ clsAlg ⌈ algOrn D R ⌉ ◇⁺) (Ṙ-preserves-comp D (fun⁺ g) (fun⁺ g º⁺))) ⟩
                 fun⁺ h •⁺ clsAlg ⌈ algOrn D R ⌉ •⁺ Ṙ D (fun⁺ g •⁺ fun⁺ g º⁺)
                   ≃⁺⟨ ≃⁺-chain-l (fun⁺ h ▪⁺ clsAlg ⌈ algOrn D R ⌉ ◇⁺) (Ṙ-cong D (iso⁺-idR⁺ gh-iso)) ⟩
                 fun⁺ h •⁺ clsAlg ⌈ algOrn D R ⌉ •⁺ Ṙ D idR⁺
                   ≃⁺⟨ ≃⁺-chain-l (fun⁺ h ▪⁺ clsAlg ⌈ algOrn D R ⌉ ◇⁺) (Ṙ-preserves-idR⁺ D) ⟩
                 fun⁺ h •⁺ clsAlg ⌈ algOrn D R ⌉ •⁺ idR⁺
                   ≃⁺⟨ •⁺-cong-l (fun⁺ h) (idR⁺-r (clsAlg ⌈ algOrn D R ⌉)) ⟩
                 fun⁺ h •⁺ clsAlg ⌈ algOrn D R ⌉
              ∎′) ⟩
       R •⁺ Ṙ D (fun⁺ h) ≃⁺ fun⁺ h •⁺ clsAlg ⌈ algOrn D R ⌉
         ⇒⟨ ≃⁺-sym ⟩
       fun⁺ h •⁺ clsAlg ⌈ algOrn D R ⌉ ≃⁺ R •⁺ Ṙ D (fun⁺ h)
    ∎) R-to-clsAlg
    where open PreorderReasoning (⇒-Preorder) renaming (_∼⟨_⟩_ to _⇒⟨_⟩_)
          setoid = ≃⁺-Setoid (Ḟ D (InvImage proj₁)) J
          open EqReasoning setoid renaming (begin_ to begin′_; _≈⟨_⟩_ to _≃⁺⟨_⟩_; _∎ to _∎′)
