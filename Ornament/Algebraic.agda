-- Definition of (relational) algebraic ornaments and classifying algebras.
-- The optimised predicate of an algebraic ornament can be swapped for a relational fold with the algebra of the ornament.

module Ornament.Algebraic where

open import Prelude.InverseImage
open import Prelude.Product
open import Prelude.Category.Isomorphism
open import Prelude.Category.Isomorphism.Functor
open import Prelude.Function
open import Prelude.Function.Fam
open import Description
open import Refinement
open import Ornament
open import Ornament.ParallelComposition
open import Ornament.RefinementSemantics
open import Relation
open import Relation.Fold

open import Function using (id; flip; _∋_)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; Σ-syntax; _,_; proj₁; proj₂; _×_; curry)
open import Data.List using (List; []; _∷_)
open import Relation.Binary using (module Setoid)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; cong; subst)
open import Relation.Binary.HeterogeneousEquality using (_≅_; ≡-to-≅) renaming (refl to hrefl)


--------
-- algebraic ornaments

algROrn : {I : Set} (D : RDesc I) {J : I → Set} → ℘ (⟦ D ⟧ J) → ROrnDesc (Σ I J) proj₁ D
algROrn (ṿ is)  {J} P = Δ[ js ∈ Ṗ is J ] Δ[ _ ∈ P js ] ṿ (Ṗ-map (λ {i} j → ok (i , j)) is js)
algROrn (σ S D)     P = σ[ s ∈ S ] algROrn (D s) (curry P s)

algOrn : ∀ {I} (D : Desc I) {J : I → Set} → (Ḟ D J ↝ J) → OrnDesc (Σ I J) proj₁ D
algOrn D R = wrap (λ { {._} (ok (i , j)) → algROrn (Desc.comp D i) (((R !!) i º⁻) j) })

algOrn-iso : {I : Set} (D : Desc I) {J : I → Set} (R : Ḟ D J ↝ J) →
             {i : I} (x : μ D i) (j : J i) → Iso Fun (OptP ⌈ algOrn D R ⌉ (ok (i , j)) x) (foldR' R i x j)
algOrn-iso {I} D {J} R =
  induction D (λ i x → (j : J i) → Iso Fun (OptP ⌈ algOrn D R ⌉ (ok (i , j)) x) (foldR' R i x j))
              (λ i ds ihs j → Setoid.trans (IsoSetoid Fun)
                               (μ-iso (OptPD ⌈ algOrn D R ⌉) (ok (i , j) , ok (i , con ds)))
                               (aux (Desc.comp D i) ds ihs (((R !!) i º⁻) j)))
  where
    aux' : (is : List I) (js : Ṗ is J) (ds : Ṗ is (μ D)) →
           All-Ṗ (λ i x → (j : J i) → Iso Fun (OptP ⌈ algOrn D R ⌉ (ok (i , j)) x) (foldR' R i x j)) is ds →
           Iso Fun (Ṗ (und-Ṗ is (pc-Ė (to≡-Ṗ is (Ṗ-map (λ {i} j → ok (i , j)) is js)) (to≡-Ṗ is (Ṗ-map (λ {i} j → ok (i , j)) is ds))))
                      (μ (OptPD ⌈ algOrn D R ⌉)))
                   (mapFoldR-Ṗ D R is ds js)
    aux' []       _        _        _          = Setoid.refl (IsoSetoid Fun)
    aux' (i ∷ is) (j , js) (d , ds) (ih , ihs) =
      Setoid.trans (IsoSetoid Fun)
        (prodIso (ih j) (aux' is js ds ihs))
        (record { to   = λ { (r , rs) → j , r , js , rs , refl }
                ; from = (Σ[ j' ∈ J i ] foldR' R i d j' × (Σ[ js' ∈ Ṗ is J ] mapFoldR-Ṗ D R is ds js' × (j' , js') ≡ (j , js)) →
                            foldR' R i d j × mapFoldR-Ṗ D R is ds js)
                           ∋ (λ { (j' , r , js' , rs , eq) → subst (foldR' R i d) (cong proj₁ eq) r ,
                                                             subst (mapFoldR-Ṗ D R is ds) (cong proj₂ eq) rs })
                           
                ; from-to-inverse = frefl
                ; to-from-inverse = λ { (.j , r , .js , rs , refl) → refl } })
    aux : (D' : RDesc I) (ds : ⟦ D' ⟧ (μ D)) → All D' (λ i x → (j : J i) → Iso Fun (OptP ⌈ algOrn D R ⌉ (ok (i , j)) x) (foldR' R i x j)) ds →
          (P : ℘ (⟦ D' ⟧ J)) →
          Iso Fun (⟦ OptPRD (toROrn (algROrn D' P)) ds ⟧ (μ (OptPD ⌈ algOrn D R ⌉))) (Σ[ js ∈ ⟦ D' ⟧ J ] mapFoldR D D' R ds js × P js)
    aux (ṿ is)   ds       ihs P =
      iso-preserving FamF
        (compIso-inv (Setoid.refl (IsoSetoid Fun))
                     (λ js → Setoid.trans (IsoSetoid Fun)
                               (iso-preserving FamF (compIso-inv (Setoid.refl (IsoSetoid Fun)) (λ _ → aux' is js ds ihs)))
                               commIso))
    aux (σ S D') (s , ds) ihs P =
      Setoid.trans (IsoSetoid Fun)
        (aux (D' s) ds ihs (curry P s))
        (record { to   = λ { (js , rs , r) → (s , js) , (js , rs , refl) , r }
                ; from = (Σ[ s'js ∈ (Σ[ s' ∈ S ] ⟦ D' s' ⟧ J) ]
                            (Σ[ js' ∈ ⟦ D' s ⟧ J ] mapFoldR D (D' s) R ds js' × (s , js') ≡ s'js) × P s'js →
                           Σ[ js ∈ ⟦ D' s ⟧ J ] mapFoldR D (D' s) R ds js × P (s , js))
                          ∋ (λ { ((.s , js) , (.js , rs , refl) , r) → js , rs , r })
                ; from-to-inverse = frefl
                ; to-from-inverse = λ { ((.s , js) , (.js , rs , refl) , r) → refl } })
   
algOrn-FSwap : ∀ {I} (D : Desc I) → ∀ {J} (R : Ḟ D J ↝ J) → FSwap (RSem' ⌈ algOrn D R ⌉)
algOrn-FSwap D R = wrap λ { {._} (ok (i , j)) → record { Q = λ x → foldR' R i x j; s = λ x → algOrn-iso D R x j } }
