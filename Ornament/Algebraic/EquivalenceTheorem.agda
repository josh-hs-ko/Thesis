-- Let `D : Desc I` be a description.
-- The category of relational `D`-algebras and the slice category of ornaments over `D` are equivalent.

module Thesis.Ornament.Algebraic.EquivalenceTheorem where

open import Thesis.Prelude.Equality
open import Thesis.Prelude.Category.Isomorphism
open import Thesis.Prelude.Category.WCat
open import Thesis.Prelude.Category.Slice
open import Thesis.Prelude.Preorder
open import Thesis.Prelude.Function
open import Thesis.Prelude.Function.Fam
open import Thesis.Prelude.Product
open import Thesis.Prelude.InverseImage
open import Thesis.Description
open import Thesis.Description.Horizontal
open import Thesis.Ornament
open import Thesis.Ornament.Category
open import Thesis.Ornament.SequentialComposition
open import Thesis.Ornament.ParallelComposition
open import Thesis.Ornament.Equivalence
open import Thesis.Ornament.Horizontal
open import Thesis.Ornament.Horizontal.Equivalence
open import Thesis.Ornament.RefinementSemantics
open import Thesis.Ornament.Algebraic
open import Thesis.Relation
open import Thesis.Relation.CompChain
open import Thesis.Relation.Fold
open import Thesis.Relation.AlgCategory

open import Function using (id; const; flip; _∘_)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_; curry; uncurry) renaming (map to _**_)
open import Data.List using (List; []; _∷_; map)
open import Relation.Binary using (module Setoid)
import Relation.Binary.PreorderReasoning as PreorderReasoning
import Relation.Binary.EqReasoning as EqReasoning
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong; cong₂) renaming (setoid to ≡-Setoid)


--------
-- the classifying predicate and algebra

Diag : {I J : Set} (e : J → I) → e ⋈ proj₁ {B = InvImage e} → Set
Diag e (j , (ok (i , j'))) = j ≡ j'

clsP : {I J : Set} {e : J → I} {D : RDesc I} {E : RDesc J} → ROrn e D E → ⟦ D ⟧ (InvImage e) → Set
clsP {e = e} O js = ⟦ OptPRD O js ⟧ (Diag e)

clsP-Ṁ : {I J : Set} {e : J → I} {is : List I} {js : List J} → Ė e js is → Ṁ (InvImage e) is → Set
clsP-Ṁ {e = e} {is} eqs js = Ṁ (Diag e) (und-Ṁ is (pc-Ė eqs (to≡-Ṁ is (Ṁ-map (λ {i} j → ok (i , j)) is js))))

clsAlg : {I J : Set} {e : J → I} {D : Desc I} {E : Desc J} (O : Orn e D E) → Ḟ D (InvImage e) ↝⁺ InvImage e
clsAlg O = wrap λ i js j → clsP (Orn.comp O j) js

-- isomorphism about the classifying predicate

from-clsP : {I J : Set} {e : J → I} {D : RDesc I} {E : RDesc J} (O : ROrn e D E) (js : ⟦ D ⟧ (InvImage e)) → clsP O js → Ṡ E
from-clsP (ṿ eqs) js        ps          = tt
from-clsP (σ S O) (s , js)  ps          = s , from-clsP (O s) js ps
from-clsP (Δ T O) js        (t , ps)    = t , from-clsP (O t) js ps
from-clsP (∇ s O) (.s , js) (refl , ps) = from-clsP O js ps

to-clsP-ṿ : {I J : Set} {e : J → I} {is : List I} {js : List J} (eqs : Ė e js is) → Σ (Ṁ (InvImage e) is) (clsP-Ṁ eqs)
to-clsP-ṿ []           = tt , tt
to-clsP-ṿ (refl ∷ eqs) = (_,_ (ok _) ** _,_ refl) (to-clsP-ṿ eqs)

to-clsP : {I J : Set} {e : J → I} {D : RDesc I} {E : RDesc J} (O : ROrn e D E) (hs : Ṡ E) → Σ (⟦ D ⟧ (InvImage e)) (clsP O)
to-clsP (ṿ eqs)  _        = to-clsP-ṿ eqs
to-clsP (σ S O) (s , hs) = (_,_ s ** id) (to-clsP (O s) hs)
to-clsP (Δ T O) (t , hs) = (id ** _,_ t) (to-clsP (O t) hs)
to-clsP (∇ s O) hs       = (_,_ s ** _,_ refl) (to-clsP O hs)

from-to-clsP-inverse : {I J : Set} {e : J → I} {D : RDesc I} {E : RDesc J} (O : ROrn e D E) → uncurry (from-clsP O) ∘ to-clsP O ≐ id
from-to-clsP-inverse (ṿ eqs)  _       = refl
from-to-clsP-inverse (σ S O) (s , hs) = cong (_,_ s) (from-to-clsP-inverse (O s) hs)
from-to-clsP-inverse (Δ T O) (t , hs) = cong (_,_ t) (from-to-clsP-inverse (O t) hs)
from-to-clsP-inverse (∇ s O) hs       = from-to-clsP-inverse O hs

to-clsP-ṿ-unique : {I J : Set} {e : J → I} {is : List I} {js : List J}
                   (eqs : Ė e js is) (js : Ṁ (InvImage e) is) (ps : _) → to-clsP-ṿ eqs ≡ (js , ps)
to-clsP-ṿ-unique []           _         _           = refl
to-clsP-ṿ-unique (refl ∷ eqs) (._ , js) (refl , ps) = cong (_,_ (ok _) ** _,_ refl) (to-clsP-ṿ-unique eqs js ps)

to-from-clsP-inverse : {I J : Set} {e : J → I} {D : RDesc I} {E : RDesc J} (O : ROrn e D E) → to-clsP O ∘ uncurry (from-clsP O) ≐ id
to-from-clsP-inverse (ṿ eqs) (js        , ps         ) = to-clsP-ṿ-unique eqs js ps
to-from-clsP-inverse (σ S O) ((s , js)  , ps         ) = cong (_,_ s ** id) (to-from-clsP-inverse (O s) (js , ps))
to-from-clsP-inverse (Δ T O) (js        , (t , ps)   ) = cong (id ** _,_ t) (to-from-clsP-inverse (O t) (js , ps))
to-from-clsP-inverse (∇ s O) ((.s , js) , (refl , ps)) = cong (_,_ s ** _,_ refl) (to-from-clsP-inverse O (js , ps))

clsP-iso : {I J : Set} {e : J → I} {D : RDesc I} {E : RDesc J} (O : ROrn e D E) → Iso Fun (Ṡ E) (Σ (⟦ D ⟧ (InvImage e)) (clsP O))
clsP-iso O = record { to   = to-clsP O
                    ; from = uncurry (from-clsP O)
                    ; from-to-inverse = from-to-clsP-inverse O
                    ; to-from-inverse = to-from-clsP-inverse O }

erase'-from-clsP : {I J : Set} {e : J → I} {D : RDesc I} {E : RDesc J} (O : ROrn e D E) (js : ⟦ D ⟧ (InvImage e)) (p : clsP O js) →
                   erase' O (const !) (from-clsP O js p) ≡ Ḣ-map D ! js
erase'-from-clsP (ṿ eqs)  _        _          = refl
erase'-from-clsP (σ S O) (s , js)  p          = cong (_,_ s) (erase'-from-clsP (O s) js p)
erase'-from-clsP (Δ T O) js        (t , p)    = erase'-from-clsP (O t) js p
erase'-from-clsP (∇ s O) (.s , js) (refl , p) = cong (_,_ s) (erase'-from-clsP O js p)

erase'-to-clsP : {I J : Set} {e : J → I} {D : RDesc I} {E : RDesc J} (O : ROrn e D E) (hs : Ṡ E) →
                 erase' O (const !) hs ≡ Ḣ-map D ! (proj₁ (to-clsP O hs))
erase'-to-clsP (ṿ eqs) hs       = refl
erase'-to-clsP (σ S O) (s , hs) = cong (_,_ s) (erase'-to-clsP (O s) hs)
erase'-to-clsP (Δ T O) (t , hs) = erase'-to-clsP (O t) hs
erase'-to-clsP (∇ s O) hs       = cong (_,_ s) (erase'-to-clsP O hs)

-- isomorphism about algROrn

algROrn-decomp : {I : Set} (D : RDesc I) (X : I → Set) (P : ℘ (⟦ D ⟧ X)) → Ṡ (toRDesc (algROrn D P)) → Σ (⟦ D ⟧ X) P
algROrn-decomp (ṿ is)  X P (xs , p , _) = xs , p
algROrn-decomp (σ S D) X P (s , hs)     = (_,_ s ** id) (algROrn-decomp (D s) X (curry P s) hs)

algROrn-comp : {I : Set} (D : RDesc I) (X : I → Set) (P : ℘ (⟦ D ⟧ X)) → (xs : ⟦ D ⟧ X) → P xs → Ṡ (toRDesc (algROrn D P))
algROrn-comp (ṿ is)  X P xs       p = xs , p , tt
algROrn-comp (σ S D) X P (s , xs) p = s , algROrn-comp (D s) X (curry P s) xs p

algROrn-decomp-comp-inverse : {I : Set} (D : RDesc I) (X : I → Set) (P : ℘ (⟦ D ⟧ X)) → algROrn-decomp D X P ∘ uncurry (algROrn-comp D X P) ≐ id
algROrn-decomp-comp-inverse (ṿ is)  X P (xs , ps)       = refl
algROrn-decomp-comp-inverse (σ S D) X P ((s , xs) , ps) = cong (_,_ s ** id) (algROrn-decomp-comp-inverse (D s) X (curry P s) (xs , ps))

algROrn-comp-decomp-inverse : {I : Set} (D : RDesc I) (X : I → Set) (P : ℘ (⟦ D ⟧ X)) → uncurry (algROrn-comp D X P) ∘ algROrn-decomp D X P ≐ id
algROrn-comp-decomp-inverse (ṿ is)  X P (xs , p , _) = refl
algROrn-comp-decomp-inverse (σ S D) X P (s , hs)     = cong (_,_ s) (algROrn-comp-decomp-inverse (D s) X (curry P s) hs)

algROrn-iso : {I : Set} (D : RDesc I) (X : I → Set) (P : ℘ (⟦ D ⟧ X)) → Iso Fun (Ṡ (toRDesc (algROrn D P))) (Σ (⟦ D ⟧ X) P)
algROrn-iso D X P = record { to   = algROrn-decomp D X P
                           ; from = uncurry (algROrn-comp D X P)
                           ; from-to-inverse = algROrn-comp-decomp-inverse D X P
                           ; to-from-inverse = algROrn-decomp-comp-inverse D X P }

erase'-algROrn-decomp : {I : Set} (D : RDesc I) (X : I → Set) (P : ℘ (⟦ D ⟧ X)) (hs : Ṡ (toRDesc (algROrn D P))) →
                        erase' (toROrn (algROrn D P)) (const !) hs ≡ Ḣ-map D ! (proj₁ (algROrn-decomp D X P hs))
erase'-algROrn-decomp (ṿ is)  X P _        = refl
erase'-algROrn-decomp (σ S D) X P (s , hs) = cong (_,_ s) (erase'-algROrn-decomp (D s) X (curry P s) hs)

erase'-algROrn-comp : {I : Set} (D' : RDesc I) (X : I → Set) (P : ℘ (⟦ D' ⟧ X)) (xs : ⟦ D' ⟧ X) (p : P xs) →
                      erase' (toROrn (algROrn D' P)) (const !) (algROrn-comp D' X P xs p) ≡ Ḣ-map D' ! xs
erase'-algROrn-comp (ṿ is)  X P xs       p = refl
erase'-algROrn-comp (σ S D) X P (s , xs) p = cong (_,_ s) (erase'-algROrn-comp (D s) X (curry P s) xs p)


--------
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

  toAlgOrn-Ė : {is : List I} {js : List J} (eqs : Ė e js is) (js' : Ṁ (InvImage e) is) → clsP-Ṁ eqs js' →
               Ė g (und-Ṁ is (Ṁ-map (λ {i} j → ok (i , j)) is js')) js
  toAlgOrn-Ė []           _          _           = []
  toAlgOrn-Ė (refl ∷ eqs) (._ , js') (refl , ps) = refl ∷ toAlgOrn-Ė eqs js' ps

  toAlgOrn-c : {D' : RDesc I} {E' : RDesc J} (O' : ROrn e D' E') (P : ℘ (⟦ D' ⟧ (InvImage e)))
               (hs : Ṡ (toRDesc (algROrn D' P))) (ps : clsP O' (proj₁ (algROrn-decomp D' (InvImage e) P hs))) →
               Ė g (next (toRDesc (algROrn D' P)) hs) (next E' (from-clsP O' (proj₁ (algROrn-decomp D' (InvImage e) P hs)) ps))
  toAlgOrn-c (ṿ eqs)  P (js , p , _) ps          = toAlgOrn-Ė eqs js ps
  toAlgOrn-c (σ S O') P (s , hs)     ps          = toAlgOrn-c (O' s) (curry P s) hs ps
  toAlgOrn-c (Δ T O') P hs           (t , ps)    = toAlgOrn-c (O' t) P hs ps
  toAlgOrn-c (∇ s O') P (.s , hs)    (refl , ps) = toAlgOrn-c O' (curry P s) hs ps

  toAlgOrn-t : (i : I) (j : e ⁻¹ i) → ḢTrans g (Desc.comp E (und j)) (toRDesc (algROrn (Desc.comp D i) (((clsAlg O !!) i º) j)))
  toAlgOrn-t i j =
    uncurry (from-clsP (Orn.comp O j)) ∘ algROrn-decomp (Desc.comp D i) (InvImage e) (((clsAlg O !!) i º) j) ,
    λ hs → toAlgOrn-c (Orn.comp O j) (((clsAlg O !!) i º) j) hs (proj₂ (algROrn-decomp (Desc.comp D i) (InvImage e) (((clsAlg O !!) i º) j) hs))

  toAlgOrn : Orn g E ⌊ algOrn D (clsAlg O) ⌋
  toAlgOrn = wrap λ { {._} (ok (i , j)) → ḢROrn (toAlgOrn-t i j) }

  toAlgOrn-triangle : OrnEq (O ⊙ toAlgOrn) ⌈ algOrn D (clsAlg O) ⌉
  toAlgOrn-triangle =
    OrnEq-trans (O ⊙ toAlgOrn) (normOrn O ⊙ toAlgOrn) ⌈ algOrn D (clsAlg O) ⌉
      (⊙-cong-r toAlgOrn O (normOrn O) (OrnEq-sym (normOrn O) O (OrnEq-normal O)))
      (OrnEq-trans (normOrn O ⊙ toAlgOrn) (normOrn ⌈ algOrn D (clsAlg O) ⌉) ⌈ algOrn D (clsAlg O) ⌉
         (to≡ ∘ proj₂ ,
          λ { (._ , ok j) →
              ROrnEq-trans (Orn.comp (normOrn O ⊙ toAlgOrn) (ok (e j , ok j)))
                           (ḢROrn (ḢTrans-normal (Orn.comp O (ok j)) ⊡ toAlgOrn-t (e j) (ok j)))
                           (Orn.comp (normOrn ⌈ algOrn D (clsAlg O) ⌉) (ok (e j , ok j)))
                (ROrnEq-sym (ḢROrn (ḢTrans-normal (Orn.comp O (ok j)) ⊡ toAlgOrn-t (e j) (ok j)))
                            (Orn.comp (normOrn O ⊙ toAlgOrn) (ok (e j , ok j)))
                   (ḢROrn-comp (ḢTrans-normal (Orn.comp O (ok j))) (toAlgOrn-t (e j) (ok j))))
                (ḢROrn-≐ (ḢTrans-normal (Orn.comp O (ok j)) ⊡ toAlgOrn-t (e j) (ok j))
                         (ḢTrans-normal (Orn.comp ⌈ algOrn D (clsAlg O) ⌉ (ok (e j , ok j))))
                   (λ hs → trans (uncurry (erase'-from-clsP (Orn.comp O (ok j)))
                                    (algROrn-decomp (Desc.comp D (e j)) (InvImage e) (((clsAlg O !!) (e j) º) (ok j)) hs))
                                 (sym (erase'-algROrn-decomp (Desc.comp D (e j)) (InvImage e) (((clsAlg O !!) (e j) º) (ok j)) hs)))) })
         (OrnEq-normal ⌈ algOrn D (clsAlg O) ⌉))

  fromAlgOrn-c-ṿ : {is : List I} {js : List J} (eqs : Ė e js is) →
                   Ė h js (und-Ṁ is (Ṁ-map (λ {i} j → ok (i , j)) is (proj₁ (to-clsP-ṿ eqs))))
  fromAlgOrn-c-ṿ []           = []
  fromAlgOrn-c-ṿ (refl ∷ eqs) = refl ∷ fromAlgOrn-c-ṿ eqs

  fromAlgOrn-c :
    {D' : RDesc I} {E' : RDesc J} (O' : ROrn e D' E') (P : ℘ (⟦ D' ⟧ (InvImage e))) (hs : Ṡ E') (p : P (proj₁ (to-clsP O' hs))) →
    Ė h (next E' hs) (next (toRDesc (algROrn D' P)) (algROrn-comp D' (InvImage e) P (proj₁ (to-clsP O' hs)) p))
  fromAlgOrn-c (ṿ eqs)  P hs       p = fromAlgOrn-c-ṿ eqs
  fromAlgOrn-c (σ S O') P (s , hs) p = fromAlgOrn-c (O' s) (curry P s) hs p
  fromAlgOrn-c (Δ T O') P (t , hs) p = fromAlgOrn-c (O' t) P hs p
  fromAlgOrn-c (∇ s O') P hs       p = fromAlgOrn-c O' (curry P s) hs p

  fromAlgOrn-t : (j : J) → ḢTrans h (toRDesc (algROrn (Desc.comp D (e j)) (((clsAlg O !!) (e j) º) (ok j)))) (Desc.comp E j)
  fromAlgOrn-t j =
    uncurry (algROrn-comp (Desc.comp D (e j)) (InvImage e) (((clsAlg O !!) (e j) º) (ok j))) ∘ to-clsP (Orn.comp O (ok j)) ,
    λ hs → fromAlgOrn-c (Orn.comp O (ok j)) (((clsAlg O !!) (e j) º) (ok j)) hs (proj₂ (to-clsP (Orn.comp O (ok j)) hs))

  fromAlgOrn : Orn h ⌊ algOrn D (clsAlg O) ⌋ E
  fromAlgOrn = wrap (λ { {._} (ok j) → ḢROrn (fromAlgOrn-t j) })

  fromAlgOrn-triangle : OrnEq (⌈ algOrn D (clsAlg O) ⌉ ⊙ fromAlgOrn) O
  fromAlgOrn-triangle =
    OrnEq-trans (⌈ algOrn D (clsAlg O) ⌉ ⊙ fromAlgOrn) (normOrn ⌈ algOrn D (clsAlg O) ⌉ ⊙ fromAlgOrn) O
      (⊙-cong-r fromAlgOrn ⌈ algOrn D (clsAlg O) ⌉ (normOrn ⌈ algOrn D (clsAlg O) ⌉)
         (OrnEq-sym (normOrn ⌈ algOrn D (clsAlg O) ⌉) ⌈ algOrn D (clsAlg O) ⌉ (OrnEq-normal ⌈ algOrn D (clsAlg O) ⌉)))
      (OrnEq-trans (normOrn ⌈ algOrn D (clsAlg O) ⌉ ⊙ fromAlgOrn) (normOrn O) O
         (frefl ,
          λ j → ROrnEq-trans (Orn.comp (normOrn ⌈ algOrn D (clsAlg O) ⌉ ⊙ fromAlgOrn) (ok j))
                             (ḢROrn (ḢTrans-normal (Orn.comp ⌈ algOrn D (clsAlg O) ⌉ (ok (e j , ok j))) ⊡ fromAlgOrn-t j))
                             (Orn.comp (normOrn O) (ok j))
                  (ROrnEq-sym (ḢROrn (ḢTrans-normal (Orn.comp ⌈ algOrn D (clsAlg O) ⌉ (ok (e j , ok j))) ⊡ fromAlgOrn-t j))
                              (Orn.comp (normOrn ⌈ algOrn D (clsAlg O) ⌉ ⊙ fromAlgOrn) (ok j))
                     (ḢROrn-comp (ḢTrans-normal (Orn.comp ⌈ algOrn D (clsAlg O) ⌉ (ok (e j , ok j)))) (fromAlgOrn-t j)))
                  (ḢROrn-≐ (ḢTrans-normal (Orn.comp ⌈ algOrn D (clsAlg O) ⌉ (ok (e j , ok j))) ⊡ fromAlgOrn-t j)
                           (ḢTrans-normal (Orn.comp O (ok j)))
                     (λ hs → trans (uncurry (erase'-algROrn-comp (Desc.comp D (e j)) (InvImage e) (((clsAlg O !!) (e j) º) (ok j)))
                                      (to-clsP (Orn.comp O (ok j)) hs))
                                   (sym (erase'-to-clsP (Orn.comp O (ok j)) hs)))))
         (OrnEq-normal O))

  toAlgOrn-fromAlgOrn-inverse : OrnEq (toAlgOrn ⊙ fromAlgOrn) (idOrn E)
  toAlgOrn-fromAlgOrn-inverse =
    gh-inverse ,
    (λ j → ROrnEq-trans (Orn.comp (toAlgOrn ⊙ fromAlgOrn) (ok j)) (ḢROrn ḢTrans-id) (Orn.comp (idOrn E) (ok j))
             (ROrnEq-trans (Orn.comp (toAlgOrn ⊙ fromAlgOrn) (ok j)) (ḢROrn (toAlgOrn-t (e j) (ok j) ⊡ fromAlgOrn-t j)) (ḢROrn ḢTrans-id)
                (ROrnEq-sym (ḢROrn (toAlgOrn-t (e j) (ok j) ⊡ fromAlgOrn-t j)) (Orn.comp (toAlgOrn ⊙ fromAlgOrn) (ok j))
                   (ḢROrn-comp (toAlgOrn-t (e j) (ok j)) (fromAlgOrn-t j)))
                (ḢROrn-≐ (toAlgOrn-t (e j) (ok j) ⊡ fromAlgOrn-t j) ḢTrans-id
                   (ftrans (fcong-l (uncurry (from-clsP (Orn.comp O (ok j))))
                              (fcong-r (to-clsP (Orn.comp O (ok j)))
                                 (algROrn-decomp-comp-inverse (Desc.comp D (e j)) (InvImage e) (((clsAlg O !!) (e j) º) (ok j)))))
                           (from-to-clsP-inverse (Orn.comp O (ok j))))))
             (ḢROrn-id {J} {Desc.comp E j}))

  fromAlgOrn-toAlgOrn-inverse : OrnEq (fromAlgOrn ⊙ toAlgOrn) (idOrn ⌊ algOrn D (clsAlg O) ⌋)
  fromAlgOrn-toAlgOrn-inverse =
    hg-inverse ,
    (λ { (._ , ok j) →
         ROrnEq-trans (Orn.comp (fromAlgOrn ⊙ toAlgOrn) (ok (e j , ok j)))
                      (ḢROrn ḢTrans-id)
                      ((Orn.comp (idOrn ⌊ algOrn D (clsAlg O) ⌋) (ok (e j , ok j))))
           (ROrnEq-trans (Orn.comp (fromAlgOrn ⊙ toAlgOrn) (ok (e j , ok j)))
                         (ḢROrn (fromAlgOrn-t j ⊡ toAlgOrn-t (e j) (ok j)))
                         (ḢROrn ḢTrans-id)
              (ROrnEq-sym (ḢROrn (fromAlgOrn-t j ⊡ toAlgOrn-t (e j) (ok j))) (Orn.comp (fromAlgOrn ⊙ toAlgOrn) (ok (e j , ok j)))
                 (ḢROrn-comp (fromAlgOrn-t j) (toAlgOrn-t (e j) (ok j))))
              (ḢROrn-≐ (fromAlgOrn-t j ⊡ toAlgOrn-t (e j) (ok j)) ḢTrans-id
                 (ftrans (fcong-l (uncurry (algROrn-comp (Desc.comp D (e j)) (InvImage e) (((clsAlg O !!) (e j) º) (ok j))))
                            (fcong-r (algROrn-decomp (Desc.comp D (e j)) (InvImage e) (((clsAlg O !!) (e j) º) (ok j)))
                               (to-from-clsP-inverse (Orn.comp O (ok j)))))
                         (algROrn-comp-decomp-inverse (Desc.comp D (e j)) (InvImage e) (((clsAlg O !!) (e j) º) (ok j))))))
           (ḢROrn-id {Σ I (InvImage e)} {Desc.comp ⌊ algOrn D (clsAlg O) ⌋ (e j , ok j)}) })


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

  CAAO-computation-ṿ : (is : List I) (js : Ṁ J is) → clsP-Ṁ (to≡-Ṁ is (Ṁ-map g is js)) (Ṁ-map g is js)
  CAAO-computation-ṿ []       _        = tt
  CAAO-computation-ṿ (i ∷ is) (j , js) = refl , CAAO-computation-ṿ is js

  CAAO-computation : (D' : RDesc I) (P : ℘ (⟦ D' ⟧ J)) (js : ⟦ D' ⟧ J) → P js → clsP (toROrn (algROrn D' P)) (mapF D' g js)
  CAAO-computation (ṿ is)   P js       p = js , p , CAAO-computation-ṿ is js
  CAAO-computation (σ S D') P (s , js) p = CAAO-computation (D' s) (curry P s) js p

  CAAO-extraction-ṿ : (is : List I) (js js' : Ṁ J is) → clsP-Ṁ (to≡-Ṁ is (Ṁ-map g is js')) (Ṁ-map g is js) → js ≡ js'
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
      aux : ∀ {i} (js : Ḟ D J i) (ij : proj₁ {B = J} ⁻¹ i) (ijs : Ḟ D (InvImage proj₁) i) (rs : mapR (Desc.comp D i) (fun⁺ g) js ijs) →
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

{-

OrnEq-to-hom :
  {I J K : Set} {e : J → I} {f : K → I} {D : Desc I} {E : Desc J} {F : Desc K} (O : Orn e D E) (P : Orn f D F) →
  {g : J → K} (Q : Orn g F E) → OrnEq O (P ⊙ Q) → Σ[ h ∶ InvImage e ⇉ InvImage f ] fun⁺ h •⁺ clsAlg O ⊆⁺ clsAlg P •⁺ Ṙ D (fun⁺ h)
OrnEq-to-hom {I} {J} {K} {e} {f} {D} {E} {F} O P {g} Q (eeq , oeq) =
  h , wrap (λ i → wrap λ { js ._ (j , p , refl) → Ḟ-map D h js , mapR-fun-computation (Desc.comp D i) h js , {!proj₂ (to-clsP (Orn.comp P (ok (g (und j)))) (erase' (Orn.comp Q (ok (und j))) (const !) (from-clsP (Orn.comp O j) js p)))!} })  -- Ṡ (Desc.comp F (g (und j)))
  where
    h : {i : I} → e ⁻¹ i → f ⁻¹ i
    h j = from≡ f (trans (sym (eeq (und j))) (to≡ j))

--------
-- the equivalence theorem

equivalence-theorem : {I : Set} (D : Desc I) → CatEquiv (RAlg' D) (SliceCategory Ōrn (I , D))
equivalence-theorem D = {!!}

-}
