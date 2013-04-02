-- Definition of (relational) algebraic ornaments and classifying algebras.
-- The optimised predicate of an algebraic ornament can be swapped for a relational fold with the algebra of the ornament.

module Thesis.Ornament.Algebraic where

open import Thesis.Prelude.InverseImage
open import Thesis.Prelude.Product
open import Thesis.Prelude.Category.Isomorphism
open import Thesis.Prelude.Category.Isomorphism.Functor
open import Thesis.Prelude.Function
open import Thesis.Prelude.Function.Fam
open import Thesis.Description
open import Thesis.Refinement
open import Thesis.Ornament
open import Thesis.Ornament.ParallelComposition
open import Thesis.Ornament.RefinementSemantics
open import Thesis.Relation
open import Thesis.Relation.Fold

open import Function using (id; flip; type-signature)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_; curry)
open import Data.List using (List; []; _∷_)
open import Relation.Binary using (module Setoid)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; cong; subst)
open import Relation.Binary.HeterogeneousEquality using (_≅_; ≡-to-≅) renaming (refl to hrefl)


--------
-- algebraic ornaments

algROrn : {I : Set} (D : RDesc I) {J : I → Set} → ℘ (⟦ D ⟧ J) → ROrnDesc (Σ I J) proj₁ D
algROrn (ṿ is)  {J} P = Δ[ js ∶ Ṁ J is ] Δ[ r ∶ P js ] ṿ (Ṁ-map (λ {i} j → ok (i , j)) is js)
algROrn (σ S D)     P = σ[ s ∶ S ] algROrn (D s) (curry P s)

algOrn : ∀ {I} (D : Desc I) {J : I → Set} → (Ḟ D J ↝⁺ J) → OrnDesc (Σ I J) proj₁ D
algOrn D R = wrap (λ { {._} (ok (i , j)) → algROrn (Desc.comp D i) (((R !!) i º) j) })

algOrn-iso : {I : Set} (D : Desc I) {J : I → Set} (R : Ḟ D J ↝⁺ J) →
             {i : I} (x : μ D i) (j : J i) → Iso Fun (OptP ⌈ algOrn D R ⌉ (ok (i , j)) x) (foldR' R i x j)
algOrn-iso {I} D {J} R =
  induction D (λ i x → (j : J i) → Iso Fun (OptP ⌈ algOrn D R ⌉ (ok (i , j)) x) (foldR' R i x j))
              (λ i ds ihs j → Setoid.trans (IsoSetoid Fun)
                               (μ-iso (OptPD ⌈ algOrn D R ⌉) (ok (i , j) , ok (i , con ds)))
                               (aux (Desc.comp D i) ds ihs (((R !!) i º) j)))
  where
    aux' : (is : List I) (js : Ṁ J is) (ds : Ṁ (μ D) is) →
           All-Ṁ (λ i x → (j : J i) → Iso Fun (OptP ⌈ algOrn D R ⌉ (ok (i , j)) x) (foldR' R i x j)) is ds →
           Iso Fun (Ṁ (μ (OptPD ⌈ algOrn D R ⌉))
                      (und-Ṁ is (pc-Ė (to≡-Ṁ is (Ṁ-map (λ {i} j → ok (i , j)) is js)) (to≡-Ṁ is (Ṁ-map (λ {i} j → ok (i , j)) is ds)))))
                   (mapFoldR-Ṁ D R is ds js)
    aux' []       _        _        _          = Setoid.refl (IsoSetoid Fun)
    aux' (i ∷ is) (j , js) (d , ds) (ih , ihs) =
      Setoid.trans (IsoSetoid Fun)
        (prodIso (ih j) (aux' is js ds ihs))
        (record { to   = λ { (r , rs) → j , r , js , rs , refl }
                ; from = (λ { (j' , r , js' , rs , eq) → subst (foldR' R i d) (cong proj₁ eq) r ,
                                                         subst (mapFoldR-Ṁ D R is ds) (cong proj₂ eq) rs }) ∶
                           (Σ[ j' ∶ J i ] foldR' R i d j' × (Σ[ js' ∶ Ṁ J is ] mapFoldR-Ṁ D R is ds js' × (j' , js') ≡ (j , js)) →
                            foldR' R i d j × mapFoldR-Ṁ D R is ds js)
                ; from-to-inverse = frefl
                ; to-from-inverse = λ { (.j , r , .js , rs , refl) → refl } })
    aux : (D' : RDesc I) (ds : ⟦ D' ⟧ (μ D)) → All D' (λ i x → (j : J i) → Iso Fun (OptP ⌈ algOrn D R ⌉ (ok (i , j)) x) (foldR' R i x j)) ds →
          (P : ℘ (⟦ D' ⟧ J)) →
          Iso Fun (⟦ OptPRD (toROrn (algROrn D' P)) ds ⟧ (μ (OptPD ⌈ algOrn D R ⌉))) (Σ[ js ∶ ⟦ D' ⟧ J ] mapFoldR D D' R ds js × P js)
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
                ; from = (λ { ((.s , js) , (.js , rs , refl) , r) → js , rs , r }) ∶
                           (Σ[ s'js ∶ (Σ[ s' ∶ S ] ⟦ D' s' ⟧ J) ]
                              (Σ[ js' ∶ ⟦ D' s ⟧ J ] mapFoldR D (D' s) R ds js' × (s , js') ≡ s'js) × P s'js →
                            Σ[ js ∶ ⟦ D' s ⟧ J ] mapFoldR D (D' s) R ds js × P (s , js))
                ; from-to-inverse = frefl
                ; to-from-inverse = λ { ((.s , js) , (.js , rs , refl) , r) → refl } })
   
algOrn-FSwap : ∀ {I} (D : Desc I) → ∀ {J} (R : Ḟ D J ↝⁺ J) → FSwap (RSem' ⌈ algOrn D R ⌉)
algOrn-FSwap D R = wrap λ { {._} (ok (i , j)) → record { Q = λ x → foldR' R i x j; s = λ x → algOrn-iso D R x j } }
