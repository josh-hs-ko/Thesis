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

open import Function using (id; type-signature)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary using (Setoid)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym)
open import Relation.Binary.HeterogeneousEquality using (_≅_; ≡-to-≅) renaming (refl to hrefl)


--------
-- algebraic ornaments

algOrn : ∀ {I} (D : Desc I) → ∀ {J} → (Ḟ D J ↝ J) → OrnDesc (Σ I J) proj₁ D
algOrn D {J} R = wrap λ { {._} (ok (i , j)) → Δ[ js ∶ Ḟ D J i ] Δ[ r ∶ Λ R js j ] erode (D at i) js }

algOrn-iso : ∀ {I} (D : Desc I) → ∀ {J} (R : Ḟ D J ↝ J) →
             ∀ {i} (x : μ D i) → ∀ {j} → Iso Fun (OptP ⌈ algOrn D R ⌉ (ok (i , j)) x) (Λ (foldR R) x j)
algOrn-iso {I} D {J} R =
  induction D (λ {i} x → ∀ {j} → Iso Fun (OptP ⌈ algOrn D R ⌉ (ok (i , j)) x) (Λ (foldR R) x j))
    (λ {i} xs all {j} →
       Setoid.trans (IsoSetoid Fun)
         (μ-iso (OptPD ⌈ algOrn D R ⌉) (ok (i , j) , ok (i , con xs)))
         (iso-preserving FamF (compIso-inv (Setoid.refl (IsoSetoid Fun))
            (λ js → Setoid.trans (IsoSetoid Fun)
                      (iso-preserving FamF (compIso-inv (Setoid.refl (IsoSetoid Fun)) (λ _ → aux (D at i) xs all js)))
                      commIso))))
  where
    aux-σ-to :
      {S : Set} (D' : S → RDesc I) (s : S) (xs : ⟦ D' s ⟧ (μ D)) (s' : S) (js : ⟦ D' s' ⟧ J) →
      ((js' : ⟦ D' s ⟧ J) → Iso Fun (⟦ OptPRD (toROrn (erode (D' s) js')) xs ⟧ (μ (OptPD ⌈ algOrn D R ⌉))) (mapFoldR D (D' s) R xs js')) →
      Σ[ eq ∶ s' ≡ s ] ⟦ toRDesc (pcROrn-double∇ (toROrn (erode (D' s') js)) (toROrn (erode (D' s) xs)) eq) ⟧ (μ (OptPD ⌈ algOrn D R ⌉)) →
      Σ[ js' ∶ ⟦ D' s ⟧ J ] mapFoldR D (D' s) R xs js' × (((s , js') ∶ (Σ[ s ∶ S ] ⟦ D' s ⟧ J)) ≡ (s' , js))
    aux-σ-to D' s xs .s js iso (refl , ps) = js , Iso.to Fun (iso js) ps , refl
    aux-σ-from :
      {S : Set} (D' : S → RDesc I) (s : S) (xs : ⟦ D' s ⟧ (μ D)) (s' : S) (js : ⟦ D' s' ⟧ J) →
      ((js' : ⟦ D' s ⟧ J) → Iso Fun (⟦ OptPRD (toROrn (erode (D' s) js')) xs ⟧ (μ (OptPD ⌈ algOrn D R ⌉))) (mapFoldR D (D' s) R xs js')) →
      Σ[ js' ∶ ⟦ D' s ⟧ J ] mapFoldR D (D' s) R xs js' × (((s , js') ∶ (Σ[ s ∶ S ] ⟦ D' s ⟧ J)) ≡ (s' , js)) →
      Σ[ eq ∶ s' ≡ s ] ⟦ toRDesc (pcROrn-double∇ (toROrn (erode (D' s') js)) (toROrn (erode (D' s) xs)) eq) ⟧ (μ (OptPD ⌈ algOrn D R ⌉))
    aux-σ-from D' s xs .s js iso (.js , rs , refl) = refl , Iso.from Fun (iso js) rs
    aux-σ-to-from-inverse :
      {S : Set} (D' : S → RDesc I) (s : S) (xs : ⟦ D' s ⟧ (μ D)) (s' : S) (js : ⟦ D' s' ⟧ J) →
      (iso : (js' : ⟦ D' s ⟧ J) → Iso Fun (⟦ OptPRD (toROrn (erode (D' s) js')) xs ⟧ (μ (OptPD ⌈ algOrn D R ⌉))) (mapFoldR D (D' s) R xs js')) →
      (p : Σ[ js' ∶ ⟦ D' s ⟧ J ] mapFoldR D (D' s) R xs js' × (((s , js') ∶ (Σ[ s ∶ S ] ⟦ D' s ⟧ J)) ≡ (s' , js))) →
      aux-σ-to D' s xs s' js iso (aux-σ-from D' s xs s' js iso p) ≡ p
    aux-σ-to-from-inverse D' s xs .s js iso (.js , rs , refl) = cong₂-pair refl (≡-to-≅ (cong₂-pair (Iso.to-from-inverse Fun (iso js) rs) hrefl))
    aux-σ-from-to-inverse :
      {S : Set} (D' : S → RDesc I) (s : S) (xs : ⟦ D' s ⟧ (μ D)) (s' : S) (js : ⟦ D' s' ⟧ J) →
      (iso : (js' : ⟦ D' s ⟧ J) → Iso Fun (⟦ OptPRD (toROrn (erode (D' s) js')) xs ⟧ (μ (OptPD ⌈ algOrn D R ⌉))) (mapFoldR D (D' s) R xs js')) →
      (p : Σ[ eq ∶ s' ≡ s ] ⟦ toRDesc (pcROrn-double∇ (toROrn (erode (D' s') js)) (toROrn (erode (D' s) xs)) eq) ⟧ (μ (OptPD ⌈ algOrn D R ⌉))) →
      aux-σ-from D' s xs s' js iso (aux-σ-to D' s xs s' js iso p) ≡ p
    aux-σ-from-to-inverse D' s xs .s js iso (refl , ps) = cong₂-pair refl (≡-to-≅ (Iso.from-to-inverse Fun (iso js) ps))
    aux-* : {A B : Set} {X : A → Set} {Y : B → Set} →
            (a : A) → X a → (b : B) → Y b → {a' : A} {b' : B} → (a , b ∶ A × B) ≡ (a' , b') → X a' × Y b'
    aux-* a x b y refl = x , y
    aux-*-inv :
      {A B : Set} {X : A → Set} {Y : B → Set} →
      (a : A) (x : X a) (b : B) (y : Y b) {a' : A} {b' : B} (eq : (a , b ∶ A × B) ≡ (a' , b')) →
      ((a' , proj₁ (aux-* {Y = Y} a x b y eq) , b' , proj₂ (aux-* {X = X} a x b y eq) , refl)
        ∶ (Σ[ a ∶ A ] X a × (Σ[ b ∶ B ] Y b × ((a , b ∶ A × B) ≡ (a' , b')))))
        ≡ (a , x , b , y , eq)
    aux-*-inv a x b y refl = refl
    aux : (D' : RDesc I) (xs : ⟦ D' ⟧ (μ D))
          (all : All D' (λ {i} x → ∀ {j} → Iso Fun (OptP ⌈ algOrn D R ⌉ (ok (i , j)) x) (Λ (foldR R) x j)) xs) (js : ⟦ D' ⟧ J) →
          Iso Fun (⟦ OptPRD (toROrn (erode D' js)) xs ⟧ (μ (OptPD ⌈ algOrn D R ⌉))) (mapFoldR D D' R xs js)
    aux ∎ xs all js = Setoid.refl (IsoSetoid Fun)
    aux (ṿ i) x all j = all
    aux (σ S D') (s , xs) all (s' , js) =
      record { to   = aux-σ-to   D' s xs s' js (aux (D' s) xs all)
             ; from = aux-σ-from D' s xs s' js (aux (D' s) xs all)
             ; to-from-inverse = aux-σ-to-from-inverse D' s xs s' js (aux (D' s) xs all)
             ; from-to-inverse = aux-σ-from-to-inverse D' s xs s' js (aux (D' s) xs all) }
    aux (D' * E') (xs , xs') (all , all') (js , js') =
      Setoid.trans (IsoSetoid Fun)
        (prodIso (aux D' xs all js) (aux E' xs' all' js'))
        (record { to   = λ { (r , r') → js , r , js' , r' , refl }
                ; from = λ p → aux-* (proj₁ p) (proj₁ (proj₂ p)) (proj₁ (proj₂ (proj₂ p)))
                                     (proj₁ (proj₂ (proj₂ (proj₂ p)))) (proj₂ (proj₂ (proj₂ (proj₂ p))))
                ; to-from-inverse = λ p → aux-*-inv (proj₁ p) (proj₁ (proj₂ p)) (proj₁ (proj₂ (proj₂ p)))
                                                    (proj₁ (proj₂ (proj₂ (proj₂ p)))) (proj₂ (proj₂ (proj₂ (proj₂ p))))
                ; from-to-inverse = frefl })
   
algOrn-FSwap : ∀ {I} (D : Desc I) → ∀ {J} (R : Ḟ D J ↝ J) → FSwap (RSem' ⌈ algOrn D R ⌉)
algOrn-FSwap D R = wrap λ { {._} (ok (i , j)) → record { Q = λ x → Λ (foldR R) x j; s = λ x → algOrn-iso D R x } }


--------
-- ornamental algebras

mutual

  ornProp : ∀ {I J} {e : J → I} {D E} → ROrn e D E → ⟦ D ⟧ (_⁻¹_ e) → Set
  ornProp ∎           _          = ⊤
  ornProp (ṿ {j} idx) j'         = und j' ≡ j
  ornProp (σ S O)     (s , js)   = ornProp (O s) js
  ornProp (Δ T O)     js         = Σ[ t ∶ T ] ornProp (O t) js
  ornProp (∇ s {D} O) (s' , js)  = Σ (s ≡ s') (ornProp-∇ {D = D} O js)
  ornProp (O * P)     (js , js') = ornProp O js × ornProp P js'

  ornProp-∇ : ∀ {I J} {e : J → I} {S : Set} {D : S → RDesc I} {E} →
              ∀ {s} → ROrn e (D s) E → ∀ {s'} → ⟦ D s' ⟧ (_⁻¹_ e) → s ≡ s' → Set
  ornProp-∇ {s} O js refl = ornProp O js

ornAlg : ∀ {I J} {e : J → I} {D E} (O : Orn e D E) → Ḟ D (_⁻¹_ e) ↝ (_⁻¹_ e)
ornAlg (wrap O) = wrap λ js j → ornProp (O j) js
