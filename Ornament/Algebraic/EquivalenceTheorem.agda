-- Let `D : Desc I` be a description.
-- The category of relational `D`-algebras and the slice category of ornaments over `D` are equivalent.

module Ornament.Algebraic.EquivalenceTheorem where

open import Prelude.Equality
open import Prelude.Category
open import Prelude.Category.Isomorphism
open import Prelude.Category.WCat
open import Prelude.Category.Slice
open import Prelude.Preorder
open import Prelude.Function
open import Prelude.Function.Fam
open import Prelude.Product
open import Prelude.InverseImage
open import Description
open import Description.Horizontal
open import Ornament
open import Ornament.Category
open import Ornament.SequentialComposition
open import Ornament.ParallelComposition
open import Ornament.Equivalence
open import Ornament.Horizontal
open import Ornament.Horizontal.Equivalence
open import Ornament.Horizontal.Category
open import Ornament.RefinementSemantics
open import Ornament.Algebraic
open import Relation
open import Relation.CompChain
open import Relation.Fold
open import Relation.AlgCategory

open import Function using (id; const; flip; _∘_)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; Σ-syntax; _,_; proj₁; proj₂; _×_; curry; uncurry) renaming (map to _**_)
open import Data.List using (List; []; _∷_; map)
open import Relation.Binary using (module Setoid)
import Relation.Binary.PreorderReasoning as PreorderReasoning
import Relation.Binary.EqReasoning as EqReasoning
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong; cong₂) renaming (setoid to ≡-Setoid)
open import Relation.Binary.HeterogeneousEquality using (_≅_; ≅-to-≡) renaming (refl to hrefl; sym to hsym)


--------
-- the classifying predicate and algebra

Diag : {I J : Set} (e : J → I) → e ⋈ proj₁ {B = InvImage e} → Set
Diag e (j , (ok (i , j'))) = j ≡ j'

clsP : {I J : Set} {e : J → I} {D : RDesc I} {E : RDesc J} → ROrn e D E → ⟦ D ⟧ (InvImage e) → Set
clsP {e = e} O js = ⟦ OptPRD O js ⟧ (Diag e)

clsP-Ṗ : {I J : Set} {e : J → I} {is : List I} {js : List J} → Ė e js is → Ṗ is (InvImage e) → Set
clsP-Ṗ {e = e} {is} eqs js = Ṗ (und-Ṗ is (pc-Ė eqs (to≡-Ṗ is (Ṗ-map (λ {i} j → ok (i , j)) is js)))) (Diag e)

clsAlg : {I J : Set} {e : J → I} {D : Desc I} {E : Desc J} (O : Orn e D E) → Ḟ D (InvImage e) ↝ InvImage e
clsAlg O = wrap λ i js j → clsP (Orn.comp O j) js

-- isomorphism about the classifying predicate

from-clsP : {I J : Set} {e : J → I} {D : RDesc I} {E : RDesc J} (O : ROrn e D E) (js : ⟦ D ⟧ (InvImage e)) → clsP O js → Ṡ E
from-clsP (ṿ eqs) js        ps          = tt
from-clsP (σ S O) (s , js)  ps          = s , from-clsP (O s) js ps
from-clsP (Δ T O) js        (t , ps)    = t , from-clsP (O t) js ps
from-clsP (∇ s O) (.s , js) (refl , ps) = from-clsP O js ps

to-clsP-ṿ : {I J : Set} {e : J → I} {is : List I} {js : List J} (eqs : Ė e js is) → Σ (Ṗ is (InvImage e)) (clsP-Ṗ eqs)
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
                   (eqs : Ė e js is) (js : Ṗ is (InvImage e)) (ps : _) → to-clsP-ṿ eqs ≡ (js , ps)
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

erase-Ṡ-from-clsP : {I J : Set} {e : J → I} {D : RDesc I} {E : RDesc J} (O : ROrn e D E) (js : ⟦ D ⟧ (InvImage e)) (p : clsP O js) →
                   erase-Ṡ O (from-clsP O js p) ≡ Ḣ-map D ! js
erase-Ṡ-from-clsP (ṿ eqs)  _        _          = refl
erase-Ṡ-from-clsP (σ S O) (s , js)  p          = cong (_,_ s) (erase-Ṡ-from-clsP (O s) js p)
erase-Ṡ-from-clsP (Δ T O) js        (t , p)    = erase-Ṡ-from-clsP (O t) js p
erase-Ṡ-from-clsP (∇ s O) (.s , js) (refl , p) = cong (_,_ s) (erase-Ṡ-from-clsP O js p)

erase-Ṡ-to-clsP : {I J : Set} {e : J → I} {D : RDesc I} {E : RDesc J} (O : ROrn e D E) (hs : Ṡ E) →
                 erase-Ṡ O hs ≡ Ḣ-map D ! (proj₁ (to-clsP O hs))
erase-Ṡ-to-clsP (ṿ eqs) hs       = refl
erase-Ṡ-to-clsP (σ S O) (s , hs) = cong (_,_ s) (erase-Ṡ-to-clsP (O s) hs)
erase-Ṡ-to-clsP (Δ T O) (t , hs) = erase-Ṡ-to-clsP (O t) hs
erase-Ṡ-to-clsP (∇ s O) hs       = cong (_,_ s) (erase-Ṡ-to-clsP O hs)

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

erase-Ṡ-algROrn-decomp : {I : Set} (D : RDesc I) (X : I → Set) (P : ℘ (⟦ D ⟧ X)) (hs : Ṡ (toRDesc (algROrn D P))) →
                        erase-Ṡ (toROrn (algROrn D P)) hs ≡ Ḣ-map D ! (proj₁ (algROrn-decomp D X P hs))
erase-Ṡ-algROrn-decomp (ṿ is)  X P _        = refl
erase-Ṡ-algROrn-decomp (σ S D) X P (s , hs) = cong (_,_ s) (erase-Ṡ-algROrn-decomp (D s) X (curry P s) hs)

erase-Ṡ-algROrn-comp : {I : Set} (D' : RDesc I) (X : I → Set) (P : ℘ (⟦ D' ⟧ X)) (xs : ⟦ D' ⟧ X) (p : P xs) →
                      erase-Ṡ (toROrn (algROrn D' P)) (algROrn-comp D' X P xs p) ≡ Ḣ-map D' ! xs
erase-Ṡ-algROrn-comp (ṿ is)  X P xs       p = refl
erase-Ṡ-algROrn-comp (σ S D) X P (s , xs) p = cong (_,_ s) (erase-Ṡ-algROrn-comp (D s) X (curry P s) xs p)


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

  toAlgOrn-Ė : {is : List I} {js : List J} (eqs : Ė e js is) (js' : Ṗ is (InvImage e)) → clsP-Ṗ eqs js' →
               Ė g (und-Ṗ is (Ṗ-map (λ {i} j → ok (i , j)) is js')) js
  toAlgOrn-Ė []           _          _           = []
  toAlgOrn-Ė (refl ∷ eqs) (._ , js') (refl , ps) = refl ∷ toAlgOrn-Ė eqs js' ps

  toAlgOrn-c : {D' : RDesc I} {E' : RDesc J} (O' : ROrn e D' E') (P : ℘ (⟦ D' ⟧ (InvImage e)))
               (hs : Ṡ (toRDesc (algROrn D' P))) (ps : clsP O' (proj₁ (algROrn-decomp D' (InvImage e) P hs))) →
               Ė g (next (toRDesc (algROrn D' P)) hs) (next E' (from-clsP O' (proj₁ (algROrn-decomp D' (InvImage e) P hs)) ps))
  toAlgOrn-c (ṿ eqs)  P (js , p , _) ps          = toAlgOrn-Ė eqs js ps
  toAlgOrn-c (σ S O') P (s , hs)     ps          = toAlgOrn-c (O' s) (curry P s) hs ps
  toAlgOrn-c (Δ T O') P hs           (t , ps)    = toAlgOrn-c (O' t) P hs ps
  toAlgOrn-c (∇ s O') P (.s , hs)    (refl , ps) = toAlgOrn-c O' (curry P s) hs ps

  toAlgOrn-t : (i : I) (j : e ⁻¹ i) → ḢTrans g (Desc.comp E (und j)) (toRDesc (algROrn (Desc.comp D i) (((clsAlg O !!) i º⁻) j)))
  toAlgOrn-t i j =
    uncurry (from-clsP (Orn.comp O j)) ∘ algROrn-decomp (Desc.comp D i) (InvImage e) (((clsAlg O !!) i º⁻) j) ,
    λ hs → toAlgOrn-c (Orn.comp O j) (((clsAlg O !!) i º⁻) j) hs (proj₂ (algROrn-decomp (Desc.comp D i) (InvImage e) (((clsAlg O !!) i º⁻) j) hs))

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
                   (λ hs → trans (uncurry (erase-Ṡ-from-clsP (Orn.comp O (ok j)))
                                    (algROrn-decomp (Desc.comp D (e j)) (InvImage e) (((clsAlg O !!) (e j) º⁻) (ok j)) hs))
                                 (sym (erase-Ṡ-algROrn-decomp (Desc.comp D (e j)) (InvImage e) (((clsAlg O !!) (e j) º⁻) (ok j)) hs)))) })
         (OrnEq-normal ⌈ algOrn D (clsAlg O) ⌉))

  fromAlgOrn-c-ṿ : {is : List I} {js : List J} (eqs : Ė e js is) →
                   Ė h js (und-Ṗ is (Ṗ-map (λ {i} j → ok (i , j)) is (proj₁ (to-clsP-ṿ eqs))))
  fromAlgOrn-c-ṿ []           = []
  fromAlgOrn-c-ṿ (refl ∷ eqs) = refl ∷ fromAlgOrn-c-ṿ eqs

  fromAlgOrn-c :
    {D' : RDesc I} {E' : RDesc J} (O' : ROrn e D' E') (P : ℘ (⟦ D' ⟧ (InvImage e))) (hs : Ṡ E') (p : P (proj₁ (to-clsP O' hs))) →
    Ė h (next E' hs) (next (toRDesc (algROrn D' P)) (algROrn-comp D' (InvImage e) P (proj₁ (to-clsP O' hs)) p))
  fromAlgOrn-c (ṿ eqs)  P hs       p = fromAlgOrn-c-ṿ eqs
  fromAlgOrn-c (σ S O') P (s , hs) p = fromAlgOrn-c (O' s) (curry P s) hs p
  fromAlgOrn-c (Δ T O') P (t , hs) p = fromAlgOrn-c (O' t) P hs p
  fromAlgOrn-c (∇ s O') P hs       p = fromAlgOrn-c O' (curry P s) hs p

  fromAlgOrn-t : (j : J) → ḢTrans h (toRDesc (algROrn (Desc.comp D (e j)) (((clsAlg O !!) (e j) º⁻) (ok j)))) (Desc.comp E j)
  fromAlgOrn-t j =
    uncurry (algROrn-comp (Desc.comp D (e j)) (InvImage e) (((clsAlg O !!) (e j) º⁻) (ok j))) ∘ to-clsP (Orn.comp O (ok j)) ,
    λ hs → fromAlgOrn-c (Orn.comp O (ok j)) (((clsAlg O !!) (e j) º⁻) (ok j)) hs (proj₂ (to-clsP (Orn.comp O (ok j)) hs))

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
                     (λ hs → trans (uncurry (erase-Ṡ-algROrn-comp (Desc.comp D (e j)) (InvImage e) (((clsAlg O !!) (e j) º⁻) (ok j)))
                                      (to-clsP (Orn.comp O (ok j)) hs))
                                   (sym (erase-Ṡ-to-clsP (Orn.comp O (ok j)) hs)))))
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
                                 (algROrn-decomp-comp-inverse (Desc.comp D (e j)) (InvImage e) (((clsAlg O !!) (e j) º⁻) (ok j)))))
                           (from-to-clsP-inverse (Orn.comp O (ok j))))))
             (ḢROrn-id (Desc.comp E j)))

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
                 (ftrans (fcong-l (uncurry (algROrn-comp (Desc.comp D (e j)) (InvImage e) (((clsAlg O !!) (e j) º⁻) (ok j))))
                            (fcong-r (algROrn-decomp (Desc.comp D (e j)) (InvImage e) (((clsAlg O !!) (e j) º⁻) (ok j)))
                               (to-from-clsP-inverse (Orn.comp O (ok j)))))
                         (algROrn-comp-decomp-inverse (Desc.comp D (e j)) (InvImage e) (((clsAlg O !!) (e j) º⁻) (ok j))))))
           (ḢROrn-id (Desc.comp ⌊ algOrn D (clsAlg O) ⌋ (e j , ok j))) })


--------
-- classifying algebra derived from an algebraic ornament is isomorphic to the algebra of the ornament

module CAAO {I : Set} {J : I → Set} (D : Desc I) (R : Ḟ D J ↝ J) where

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

  CAAO-computation-ṿ : (is : List I) (js : Ṗ is J) → clsP-Ṗ (to≡-Ṗ is (Ṗ-map g is js)) (Ṗ-map g is js)
  CAAO-computation-ṿ []       _        = tt
  CAAO-computation-ṿ (i ∷ is) (j , js) = refl , CAAO-computation-ṿ is js

  CAAO-computation : (D' : RDesc I) (P : ℘ (⟦ D' ⟧ J)) (js : ⟦ D' ⟧ J) → P js → clsP (toROrn (algROrn D' P)) (mapF D' g js)
  CAAO-computation (ṿ is)   P js       p = js , p , CAAO-computation-ṿ is js
  CAAO-computation (σ S D') P (s , js) p = CAAO-computation (D' s) (curry P s) js p

  CAAO-extraction-ṿ : (is : List I) (js js' : Ṗ is J) → clsP-Ṗ (to≡-Ṗ is (Ṗ-map g is js')) (Ṗ-map g is js) → js ≡ js'
  CAAO-extraction-ṿ []       _        _          _            = refl
  CAAO-extraction-ṿ (i ∷ is) (j , js) (.j , js') (refl , eqs) = cong (_,_ j) (CAAO-extraction-ṿ is js js' eqs)

  CAAO-extraction : (D' : RDesc I) (P : ℘ (⟦ D' ⟧ J)) (js : ⟦ D' ⟧ J) → clsP (toROrn (algROrn D' P)) (mapF D' g js) → P js
  CAAO-extraction (ṿ is)   P js       (js' , p , eqs) with CAAO-extraction-ṿ is js js' eqs
  CAAO-extraction (ṿ is)   P js       (.js , p , eqs) | refl = p
  CAAO-extraction (σ S D') P (s , js) p                      = CAAO-extraction (D' s) (curry P s) js p

  R-to-clsAlg : fun g • R ≃ clsAlg ⌈ algOrn D R ⌉ • Ṙ D (fun g)
  R-to-clsAlg = wrap (λ i → wrap λ { js ._ (j , r , refl) →
                                     Ḟ-map D g js ,
                                     mapR-fun⁻-computation (Desc.comp D i) g js ,
                                     CAAO-computation (Desc.comp D i) (((R !!) i º⁻) j) js r }) ,
                wrap (λ i → wrap λ { js ij (ijs , rs , q) → aux js ij ijs rs q })
    where
      aux : ∀ {i} (js : Ḟ D J i) (ij : proj₁ {B = J} ⁻¹ i) (ijs : Ḟ D (InvImage proj₁) i) (rs : mapR (Desc.comp D i) (fun g) js ijs) →
            (q : (clsAlg ⌈ algOrn D R ⌉ !!) i ijs ij) → ((fun g • R) !!) i js ij
      aux js (ok (i , j)) ijs rs p with mapR-fun⁻-unique (Desc.comp D i) g js ijs rs
      aux js (ok (i , j)) ._  rs p | refl = j , CAAO-extraction (Desc.comp D i) (((R !!) i º⁻) j) js p , refl

  clsAlg-to-R : fun h • clsAlg ⌈ algOrn D R ⌉ ≃ R • Ṙ D (fun h)
  clsAlg-to-R =
    (begin
       fun g • R ≃ clsAlg ⌈ algOrn D R ⌉ • Ṙ D (fun g)
         ⇒⟨ •-cong-l (fun h) ⟩
       fun h • fun g • R ≃ fun h • clsAlg ⌈ algOrn D R ⌉ • Ṙ D (fun g)
         ⇒⟨ ≃-trans (≃-chain (fun h ◇) (fun h º ◇) (fun g ◇) (iso-conv (Setoid.sym (IsoSetoid Fun) ∘ gh-iso))) ⟩
       fun h • fun h º • R ≃ fun h • clsAlg ⌈ algOrn D R ⌉ • Ṙ D (fun g)
         ⇒⟨ ≃-trans (≃-sym (≃-chain-r (fun h ▪ fun h º ◇) (idR ◇) (iso-idR (Setoid.sym (IsoSetoid Fun) ∘ gh-iso)))) ⟩
       idR • R ≃ fun h • clsAlg ⌈ algOrn D R ⌉ • Ṙ D (fun g)
         ⇒⟨ ≃-trans (≃-sym (idR-l R)) ⟩
       R ≃ fun h • clsAlg ⌈ algOrn D R ⌉ • Ṙ D (fun g)
         ⇒⟨ •-cong-r (Ṙ D (fun h)) ⟩
       R • Ṙ D (fun h) ≃ (fun h • clsAlg ⌈ algOrn D R ⌉ • Ṙ D (fun g)) • Ṙ D (fun h)
         ⇒⟨ flip ≃-trans
              (begin′
                 (fun h • clsAlg ⌈ algOrn D R ⌉ • Ṙ D (fun g)) • Ṙ D (fun h)
                   ≃⟨ ≃-sym (•-cong-l (fun h • clsAlg ⌈ algOrn D R ⌉ • Ṙ D (fun g)) (Ṙ-cong D (iso-conv gh-iso))) ⟩
                 (fun h • clsAlg ⌈ algOrn D R ⌉ • Ṙ D (fun g)) • Ṙ D (fun g º)
                   ≃⟨ chain-normalise (([ fun h ] ▪ [ clsAlg ⌈ algOrn D R ⌉ ] ▪ [ Ṙ D (fun g) ]) ▪ [ Ṙ D (fun g º) ]) ⟩
                 fun h • clsAlg ⌈ algOrn D R ⌉ • Ṙ D (fun g) • Ṙ D (fun g º)
                   ≃⟨ ≃-sym (≃-chain-l (fun h ▪ clsAlg ⌈ algOrn D R ⌉ ◇) (Ṙ-preserves-comp D (fun g) (fun g º))) ⟩
                 fun h • clsAlg ⌈ algOrn D R ⌉ • Ṙ D (fun g • fun g º)
                   ≃⟨ ≃-chain-l (fun h ▪ clsAlg ⌈ algOrn D R ⌉ ◇) (Ṙ-cong D (iso-idR gh-iso)) ⟩
                 fun h • clsAlg ⌈ algOrn D R ⌉ • Ṙ D idR
                   ≃⟨ ≃-chain-l (fun h ▪ clsAlg ⌈ algOrn D R ⌉ ◇) (Ṙ-preserves-idR D) ⟩
                 fun h • clsAlg ⌈ algOrn D R ⌉ • idR
                   ≃⟨ •-cong-l (fun h) (idR-r (clsAlg ⌈ algOrn D R ⌉)) ⟩
                 fun h • clsAlg ⌈ algOrn D R ⌉
              ∎′) ⟩
       R • Ṙ D (fun h) ≃ fun h • clsAlg ⌈ algOrn D R ⌉
         ⇒⟨ ≃-sym ⟩
       fun h • clsAlg ⌈ algOrn D R ⌉ ≃ R • Ṙ D (fun h)
    ∎) R-to-clsAlg
    where open PreorderReasoning (⇒-Preorder) renaming (_∼⟨_⟩_ to _⇒⟨_⟩_)
          setoid = ≃-Setoid (Ḟ D (InvImage proj₁)) J
          open EqReasoning setoid renaming (begin_ to begin′_; _≈⟨_⟩_ to _≃⟨_⟩_; _∎ to _∎′)

next-from-clsP-ṿ :
  {I J : Set} {e : J → I} {is : List I} {js : List J} (eqs : Ė e js is) (js' : Ṗ is (InvImage e)) → clsP-Ṗ eqs js' → js ≡ und-Ṗ is js'
next-from-clsP-ṿ []           _         _          = refl
next-from-clsP-ṿ (refl ∷ eqs) (._ , js) (refl , p) = cong₂ _∷_ refl (next-from-clsP-ṿ eqs js p)

next-from-clsP :
  {I J : Set} {e : J → I} {D : RDesc I} {E : RDesc J} (O : ROrn e D E) (js : ⟦ D ⟧ (InvImage e)) (p : clsP O js) →
  next E (from-clsP O js p) ≡ uncurry (und-Ṗ ∘ next D) (Ḣ-decomp D (flip Ṗ (InvImage e)) js)
next-from-clsP (ṿ eqs) js p = next-from-clsP-ṿ eqs js p
next-from-clsP (σ S O) (s , js) p = next-from-clsP (O s) js p
next-from-clsP (Δ T O) js (t , p) = next-from-clsP (O t) js p
next-from-clsP (∇ s O) (.s , js) (refl , p) = next-from-clsP O js p

make-clsP-Ṗ :
  {I J : Set} {e : J → I} {is : List I} {js : List J} (eqs : Ė e js is) (js' : Ṗ is (InvImage e)) → js ≡ und-Ṗ is js' → clsP-Ṗ eqs js'
make-clsP-Ṗ []         _           _    = tt
make-clsP-Ṗ (eq ∷ eqs) (ok j , js) refl with eq
make-clsP-Ṗ (eq ∷ eqs) (ok j , js) refl | refl = refl , make-clsP-Ṗ eqs js refl

make-clsP : {I J : Set} {e : J → I} {D : RDesc I} {E : RDesc J} (O : ROrn e D E) (js : ⟦ D ⟧ (InvImage e))
          (hs : Ṡ E) → erase-Ṡ O hs ≡ proj₁ (Ḣ-decomp D (flip Ṗ (InvImage e)) js) →
                       next E hs ≡ uncurry (und-Ṗ ∘ next D) (Ḣ-decomp D (flip Ṗ (InvImage e)) js) → clsP O js
make-clsP (ṿ eqs) js        _         _  eq' = make-clsP-Ṗ eqs js eq'
make-clsP (σ S O) (s , js)  (s' , hs) eq eq' with cong proj₁ eq
make-clsP (σ S O) (s , js)  (.s , hs) eq eq' | refl = make-clsP (O s) js hs (cong-proj₂ eq) eq'
make-clsP (Δ T O) js        (t , hs)  eq eq' = t , make-clsP (O t) js hs eq eq'
make-clsP (∇ s O) (s' , js) hs        eq eq' with cong proj₁ eq
make-clsP (∇ s O) (.s , js) hs        eq eq' | refl = refl , make-clsP O js hs (cong-proj₂ eq) eq'

InvImage-lift : {I J K : Set} (e : J → I) (f : K → I) (g : J → K) → f ∘ g ≐ e → InvImage e ⇉ InvImage f
InvImage-lift e f g eeq j = from≡ f (trans (eeq (und j)) (to≡ j))

cong-InvImage-lift :
  {I J K : Set} (e : J → I) (f : K → I) (g : J → K) (g' : J → K) (eeq : f ∘ g ≐ e) (eeq' : f ∘ g' ≐ e) →
  g ≐ g' → {i : I} → InvImage-lift e f g eeq {i} ≐ InvImage-lift e f g' eeq' {i}
cong-InvImage-lift e f g g' eeq eeq' g≐g' j =
  und≡ (trans (und-from≡ f (trans (eeq (und j)) (to≡ j))) (trans (g≐g' (und j)) (sym (und-from≡ f (trans (eeq' (und j)) (to≡ j))))))

next-erase-Ṡ : {I J : Set} {e : J → I} {D : RDesc I} {E : RDesc J} (O : ROrn e D E) (hs : Ṡ E) → next D (erase-Ṡ O hs) ≡ map e (next E hs)
next-erase-Ṡ (ṿ eqs) hs       = Ė-unique eqs
next-erase-Ṡ (σ S O) (s , hs) = next-erase-Ṡ (O s) hs
next-erase-Ṡ (Δ T O) (t , hs) = next-erase-Ṡ (O t) hs
next-erase-Ṡ (∇ s O) hs       = next-erase-Ṡ O hs

next-from-clsP-lemma :
  {I J K : Set} (e : J → I) (f : K → I) (g : J → K) (eeq : f ∘ g ≐ e) (D : RDesc I) (js : ⟦ D ⟧ (InvImage e)) →
  map g (uncurry (und-Ṗ ∘ next D) (Ḣ-decomp D (flip Ṗ (InvImage e)) js))
    ≡ uncurry (und-Ṗ ∘ next D) (Ḣ-decomp D (flip Ṗ (InvImage f)) (mapF D (InvImage-lift e f g eeq) js))
next-from-clsP-lemma e f g eeq (ṿ [])        _           = refl
next-from-clsP-lemma e f g eeq (ṿ (._ ∷ is)) (ok j , js) = cong₂ _∷_ (sym (und-from≡ f (trans (eeq j) refl)))
                                                                     (next-from-clsP-lemma e f g eeq (ṿ is) js)
next-from-clsP-lemma e f g eeq (σ S D)       (s , js)    = next-from-clsP-lemma e f g eeq (D s) js

OrnEq-to-hom-aux :
  {I J K : Set} {e : J → I} {f : K → I} {D D' : RDesc I} {E : RDesc J} {F F' : RDesc K}
  (O : ROrn e D E) (P : ROrn f D' F) (P' : ROrn f D F') → D ≡ D' → F ≡ F' → P ≅ P' →
  {g : J → K} (Q : ROrn g F E) (eeq : f ∘ g ≐ e) (js : ⟦ D ⟧ (InvImage e)) →
  (p : clsP O js) → erase-Ṡ (scROrn P Q) (from-clsP O js p) ≅ erase-Ṡ O (from-clsP O js p) → clsP P' (mapF D (InvImage-lift e f g eeq) js)
OrnEq-to-hom-aux {e = e} {f} {D} O P .P refl refl hrefl {g} Q eeq js p eraseeq =
  make-clsP P (mapF D (InvImage-lift e f g eeq) js) (erase-Ṡ Q (from-clsP O js p))
    (trans (sym (erase-Ṡ-scROrn P Q (from-clsP O js p)))
           (trans (≅-to-≡ eraseeq) (trans (trans (erase-Ṡ-from-clsP O js p) (Ḣ-map-to-Ḣ-decomp D (flip Ṗ (InvImage e)) js))
                                          (Ḣ-map-preserves-shape D (flip Ṗ (InvImage e)) (flip Ṗ (InvImage f)) _ js))))
    (trans (next-erase-Ṡ Q (from-clsP O js p)) (trans (cong (map g) (next-from-clsP O js p)) (next-from-clsP-lemma e f g eeq D js)))

OrnEq-to-hom :
  {I J K : Set} {e : J → I} {f : K → I} {D : Desc I} {E : Desc J} {F : Desc K} (O : Orn e D E) (P : Orn f D F) →
  {g : J → K} (Q : Orn g F E) (oeq : OrnEq (P ⊙ Q) O) →
  let h : InvImage e ⇉ InvImage f; h = InvImage-lift e f g (proj₁ oeq) in fun h • clsAlg O ⊆ clsAlg P • Ṙ D (fun h)
OrnEq-to-hom {I} {J} {K} {e} {f} {D} {E} {F} O P {g} Q (eeq , roeq) =
  wrap (λ i → wrap λ { js ._ (j , p , refl) → Ḟ-map D h js , mapR-fun⁻-computation (Desc.comp D i) h js , aux js j p })
  where
    h : InvImage e ⇉ InvImage f
    h = InvImage-lift e f g eeq
    aux : {i : I} (js : ⟦ Desc.comp D i ⟧ (InvImage e)) (j : e ⁻¹ i) → clsP (Orn.comp O j) js → clsP (Orn.comp P (h j)) (Ḟ-map D h js)
    aux js (ok j) p = OrnEq-to-hom-aux (Orn.comp O (ok j)) (Orn.comp P (ok (g j))) (Orn.comp P (from≡ f (trans (eeq j) refl)))
                        (cong (Desc.comp D) (sym (eeq j))) (cong (Desc.comp F) (sym (und-from≡ f (trans (eeq j) refl))))
                        (subst (λ i → (k : f ⁻¹ i) → k ≅ ok {f = f} (g j) → Orn.comp P (ok (g j)) ≅ Orn.comp P k)
                               (eeq j) (λ { ._ hrefl → hrefl }) (from≡ f (trans (eeq j) refl))
                               (hsym (und≡' (from≡ f (trans (eeq j) refl)) (sym (und-from≡ f (trans (eeq j) refl))))))
                        (Orn.comp Q (ok j)) eeq js p (roeq j (from-clsP (Orn.comp O (ok j)) js p))

hom-to-OrnEq-aux-ṿ :
  {I : Set} (is : List I) {J K : I → Set} (js : Ṗ is J) (h : J ⇉ K) →
  Ė (id ** h) (und-Ṗ is (Ṗ-map (λ {i} j → ok (i , j)) is js)) (und-Ṗ is (Ṗ-map (λ {i} j → ok (i , j)) is (Ṗ-map h is js)))
hom-to-OrnEq-aux-ṿ []       _        h = []
hom-to-OrnEq-aux-ṿ (i ∷ is) (j , js) h = refl ∷ hom-to-OrnEq-aux-ṿ is js h

hom-to-OrnEq-aux :
  {I : Set} (D : RDesc I) {J K : I → Set} (P : ℘ (⟦ D ⟧ J)) (Q : ℘ (⟦ D ⟧ K))
  (h : J ⇉ K) → ((js : ⟦ D ⟧ J) → P js → Q (mapF D h js)) →
  ROrn (id ** h) (toRDesc (algROrn D Q)) (toRDesc (algROrn D P))
hom-to-OrnEq-aux (ṿ is)  {J} P Q h p-to-q = Δ[ js ∈ Ṗ is J ] ∇ (Ṗ-map h is js) (Δ[ p ∈ P js ] ∇ (p-to-q js p) (ṿ (hom-to-OrnEq-aux-ṿ is js h)))
hom-to-OrnEq-aux (σ S D)     P Q h p-to-q = σ[ s ∈ S ] hom-to-OrnEq-aux (D s) (curry P s) (curry Q s) h (curry p-to-q s)

hom-to-OrnEq :
  {I : Set} (D : Desc I) {J K : I → Set} (R : Ḟ D J ↝ J) (S : Ḟ D K ↝ K)
  (h : J ⇉ K) → fun h • R ⊆ S • Ṙ D (fun h) → Orn (id ** h) ⌊ algOrn D S ⌋ ⌊ algOrn D R ⌋
hom-to-OrnEq D R S h inc =
  wrap λ { {._} (ok (i , j)) →
           hom-to-OrnEq-aux (Desc.comp D i) (((R !!) i º⁻) j) (((S !!) i º⁻) (h j)) h
             (λ js r → let (ks , rs , s) = modus-ponens-⊆ inc i js (h j) (j , r , refl)
                       in  subst (((S !!) i º⁻) (h j)) (sym (mapR-fun⁻-unique (Desc.comp D i) h js ks rs)) s) }
