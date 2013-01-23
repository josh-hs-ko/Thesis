module Thesis.Ornament.Algebraic where

open import Thesis.Prelude.Equality
open import Thesis.Prelude.InverseImage
open import Thesis.Prelude.Product
open import Thesis.Prelude.Function
import Thesis.Prelude.Category.Isomorphism as Isomorphism; open Isomorphism Fun
open import Thesis.Prelude.Category.Isomorphism.Functor
open import Thesis.Prelude.Function.Fam
open import Thesis.Description
open import Thesis.Refinement
open import Thesis.Ornament
open import Thesis.Ornament.ParallelComposition
open import Thesis.Ornament.RefinementSemantics
open import Thesis.Ornament.Isomorphism
open import Thesis.Relation

open import Function using (id; _∘_; const; type-signature)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary using (Setoid)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; trans; sym) renaming (setoid to ≡-Setoid)
open import Relation.Binary.HeterogeneousEquality using (_≅_; ≡-to-≅) renaming (refl to hrefl)


--------
-- algebraic ornaments

algOrn : ∀ {I} (D : Desc I) → ∀ {J} → (Ḟ D J ↝ J) → OrnDesc (Σ I J) proj₁ D
algOrn D {J} R = wrap λ { {._} (ok (i , j)) → Δ[ js ∶ Ḟ D J i ] Δ[ r ∶ Λ R js j ] erode (D at i) js }

{-

algOrn-iso : ∀ {I} (D : Desc I) → ∀ {J} (R : Ḟ D J ↝ J) →
             ∀ {i} (x : μ D i) → ∀ {j} → Iso (OptP ⌈ algOrn D R ⌉ (ok (i , j)) x) (Λ (foldR R) x j)
algOrn-iso {I} D {J} R =
  induction D (λ {i} x → ∀ {j} → Iso (OptP ⌈ algOrn D R ⌉ (ok (i , j)) x) (Λ (foldR R) x j))
    (λ {i} xs all {j} →
       Setoid.trans IsoSetoid
         (μ-iso (OptPD ⌈ algOrn D R ⌉) (ok (i , j) , ok (i , con xs)))
         (iso-preserving FamF (compIso-inv (Setoid.refl IsoSetoid)
            (λ js → Setoid.trans IsoSetoid
                      (iso-preserving FamF (compIso-inv (Setoid.refl IsoSetoid) (λ _ → aux (D at i) xs all js)))
                      commIso))))
  where
    aux-σ-to :
      {S : Set} (D' : S → RDesc I) (s : S) (xs : ⟦ D' s ⟧ (μ D)) (s' : S) (js : ⟦ D' s' ⟧ J) →
      ((js' : ⟦ D' s ⟧ J) → Iso (⟦ OptPRD (toROrn (erode (D' s) js')) xs ⟧ (μ (OptPD ⌈ algOrn D R ⌉))) (mapFoldR D (D' s) R xs js')) →
      Σ[ eq ∶ s' ≡ s ] ⟦ toRDesc (pcROrn-double∇ (toROrn (erode (D' s') js)) (toROrn (erode (D' s) xs)) eq) ⟧ (μ (OptPD ⌈ algOrn D R ⌉)) →
      Σ[ js' ∶ ⟦ D' s ⟧ J ] mapFoldR D (D' s) R xs js' × (((s , js') ∶ (Σ[ s ∶ S ] ⟦ D' s ⟧ J)) ≡ (s' , js))
    aux-σ-to D' s xs .s js iso (refl , ps) = js , Iso.to (iso js) ps , refl
    aux-σ-from :
      {S : Set} (D' : S → RDesc I) (s : S) (xs : ⟦ D' s ⟧ (μ D)) (s' : S) (js : ⟦ D' s' ⟧ J) →
      ((js' : ⟦ D' s ⟧ J) → Iso (⟦ OptPRD (toROrn (erode (D' s) js')) xs ⟧ (μ (OptPD ⌈ algOrn D R ⌉))) (mapFoldR D (D' s) R xs js')) →
      Σ[ js' ∶ ⟦ D' s ⟧ J ] mapFoldR D (D' s) R xs js' × (((s , js') ∶ (Σ[ s ∶ S ] ⟦ D' s ⟧ J)) ≡ (s' , js)) →
      Σ[ eq ∶ s' ≡ s ] ⟦ toRDesc (pcROrn-double∇ (toROrn (erode (D' s') js)) (toROrn (erode (D' s) xs)) eq) ⟧ (μ (OptPD ⌈ algOrn D R ⌉))
    aux-σ-from D' s xs .s js iso (.js , rs , refl) = refl , Iso.from (iso js) rs
    aux-σ-to-from-inverse :
      {S : Set} (D' : S → RDesc I) (s : S) (xs : ⟦ D' s ⟧ (μ D)) (s' : S) (js : ⟦ D' s' ⟧ J) →
      (iso : (js' : ⟦ D' s ⟧ J) → Iso (⟦ OptPRD (toROrn (erode (D' s) js')) xs ⟧ (μ (OptPD ⌈ algOrn D R ⌉))) (mapFoldR D (D' s) R xs js')) →
      (p : Σ[ js' ∶ ⟦ D' s ⟧ J ] mapFoldR D (D' s) R xs js' × (((s , js') ∶ (Σ[ s ∶ S ] ⟦ D' s ⟧ J)) ≡ (s' , js))) →
      aux-σ-to D' s xs s' js iso (aux-σ-from D' s xs s' js iso p) ≡ p
    aux-σ-to-from-inverse D' s xs .s js iso (.js , rs , refl) = cong₂-pair refl (≡-to-≅ (cong₂-pair (Iso.to-from-inverse (iso js) rs) hrefl))
    aux-σ-from-to-inverse :
      {S : Set} (D' : S → RDesc I) (s : S) (xs : ⟦ D' s ⟧ (μ D)) (s' : S) (js : ⟦ D' s' ⟧ J) →
      (iso : (js' : ⟦ D' s ⟧ J) → Iso (⟦ OptPRD (toROrn (erode (D' s) js')) xs ⟧ (μ (OptPD ⌈ algOrn D R ⌉))) (mapFoldR D (D' s) R xs js')) →
      (p : Σ[ eq ∶ s' ≡ s ] ⟦ toRDesc (pcROrn-double∇ (toROrn (erode (D' s') js)) (toROrn (erode (D' s) xs)) eq) ⟧ (μ (OptPD ⌈ algOrn D R ⌉))) →
      aux-σ-from D' s xs s' js iso (aux-σ-to D' s xs s' js iso p) ≡ p
    aux-σ-from-to-inverse D' s xs .s js iso (refl , ps) = cong₂-pair refl (≡-to-≅ (Iso.from-to-inverse (iso js) ps))
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
          (all : All D' (λ {i} x → ∀ {j} → Iso (OptP ⌈ algOrn D R ⌉ (ok (i , j)) x) (Λ (foldR R) x j)) xs) (js : ⟦ D' ⟧ J) →
          Iso (⟦ OptPRD (toROrn (erode D' js)) xs ⟧ (μ (OptPD ⌈ algOrn D R ⌉))) (mapFoldR D D' R xs js)
    aux ∎ xs all js = Setoid.refl (IsoSetoid)
    aux (ṿ i) x all j = all
    aux (σ S D') (s , xs) all (s' , js) =
      record { to   = aux-σ-to   D' s xs s' js (aux (D' s) xs all)
             ; from = aux-σ-from D' s xs s' js (aux (D' s) xs all)
             ; to-from-inverse = aux-σ-to-from-inverse D' s xs s' js (aux (D' s) xs all)
             ; from-to-inverse = aux-σ-from-to-inverse D' s xs s' js (aux (D' s) xs all) }
    aux (D' * E') (xs , xs') (all , all') (js , js') =
      Setoid.trans (IsoSetoid)
        (prodIso (aux D' xs all js) (aux E' xs' all' js'))
        (record { to   = λ { (r , r') → js , r , js' , r' , refl }
                ; from = λ p → aux-* (proj₁ p) (proj₁ (proj₂ p)) (proj₁ (proj₂ (proj₂ p)))
                                     (proj₁ (proj₂ (proj₂ (proj₂ p)))) (proj₂ (proj₂ (proj₂ (proj₂ p))))
                ; to-from-inverse = λ p → aux-*-inv (proj₁ p) (proj₁ (proj₂ p)) (proj₁ (proj₂ (proj₂ p)))
                                                    (proj₁ (proj₂ (proj₂ (proj₂ p)))) (proj₂ (proj₂ (proj₂ (proj₂ p))))
                ; from-to-inverse = frefl })
   
algOrn-FSwap : ∀ {I} (D : Desc I) → ∀ {J} (R : Ḟ D J ↝ J) → FSwap (RSem' ⌈ algOrn D R ⌉)
algOrn-FSwap D R = wrap λ { {._} (ok (i , j)) → record { Q = λ x → Λ (foldR R) x j; s = λ x → algOrn-iso D R x } }

-}

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


--------
-- ornamental algebra derived from an algebraic ornament is equivalent to the original algebra

module OAAO {I : Set} {J : I → Set} (D : Desc I) (R : Ḟ D J ↝ J) where

  h : J ⇒ _⁻¹_ proj₁
  h {i} = ok ∘ _,_ i

  OAAO-theorem-aux-⊆ : (D : RDesc I) (js : ⟦ D ⟧ J) → ornProp (toROrn (erode D js)) (mapF D h js)
  OAAO-theorem-aux-⊆ ∎       js         = tt
  OAAO-theorem-aux-⊆ (ṿ i)   j          = refl
  OAAO-theorem-aux-⊆ (σ S D) (s , js)   = refl , OAAO-theorem-aux-⊆ (D s) js
  OAAO-theorem-aux-⊆ (D * E) (js , js') = OAAO-theorem-aux-⊆ D js , OAAO-theorem-aux-⊆ E js'

  OAAO-theorem-aux-⊇ : (D : RDesc I) (js js' : ⟦ D ⟧ J) → ornProp (toROrn (erode D js')) (mapF D h js) → js ≡ js'
  OAAO-theorem-aux-⊇ ∎       js        js'         p          = refl
  OAAO-theorem-aux-⊇ (ṿ i)   j         j'          p          = cong-proj₂ p
  OAAO-theorem-aux-⊇ (σ S D) (s , js)  (.s , js')  (refl , p) = cong (_,_ s) (OAAO-theorem-aux-⊇ (D s) js js' p)
  OAAO-theorem-aux-⊇ (D * E) (js , ks) (js' , ks') (p , p')   = cong₂ _,_ (OAAO-theorem-aux-⊇ D js js' p) (OAAO-theorem-aux-⊇ E ks ks' p')

  OAAO-theorem : fun h • R ≃ ornAlg ⌈ algOrn D R ⌉ • Ṙ D (fun h)
  OAAO-theorem =
    wrap (λ {i} js → wrap (λ { ._ (j , r , refl) →
                               Ḟ-map D h js , mapR-fun-computation (D at i) h js , js , r , OAAO-theorem-aux-⊆ (D at i) js })) ,
    wrap (λ {i} js → wrap (λ { ij (ijs , rs , q) → aux-⊇ js ij ijs rs q }))
    where
      aux-⊇ : ∀ {i} (js : Ḟ D J i) (ij : proj₁ {B = J} ⁻¹ i) (ijs : Ḟ D (_⁻¹_ proj₁) i) (rs : mapR (D at i) (fun h) js ijs) →
            (q : Λ (ornAlg ⌈ algOrn D R ⌉) ijs ij) → Λ (fun h • R) js ij
      aux-⊇ js (ok (i , j)) ijs rs (js' , r , p) with mapR-fun-unique (D at i) h js ijs rs
      aux-⊇ js (ok (i , j)) ._  rs (js' , r , p) | refl with OAAO-theorem-aux-⊇ (D at i) js js' p
      aux-⊇ js (ok (i , j)) ._  rs (.js , r , p) | refl | refl = j , r , refl

  g : _⁻¹_ proj₁ ⇒ J
  g (ok (i , j)) = j

  hg-inverse : ∀ {i} (ij : proj₁ ⁻¹ i) → h (g ij) ≡ ij
  hg-inverse (ok (i , j)) = refl

  hg-iso : ∀ i → Iso (J i) (proj₁ {B = J} ⁻¹ i)
  hg-iso i = record { to = h; from = g; to-from-inverse = hg-inverse; from-to-inverse = frefl }


--------
-- algebraic ornamentation with an ornamental algebra produces an isomorphic datatype

tweakOrn-aux : ∀ {I J} {e : J → I} {D' E'} (O' : ROrn e D' E') →
               (js : ⟦ D' ⟧ (_⁻¹_ e)) → ornProp O' js → ROrn (und ∘ proj₂) E' (toRDesc (erode D' js))
tweakOrn-aux ∎          ds           p          = ∎
tweakOrn-aux (ṿ idx)    j'           eq         = ṿ eq
tweakOrn-aux (σ S O')   (s , js)     p          = ∇ s (tweakOrn-aux (O' s) js p)
tweakOrn-aux (Δ T O')   js           (t , p)    = ∇ t (tweakOrn-aux (O' t) js p)
tweakOrn-aux (∇ s O')   (.s , js)    (refl , p) = tweakOrn-aux O' js p
tweakOrn-aux (O' * O'') (js' , js'') (p' , p'') = tweakOrn-aux O' js' p' * tweakOrn-aux O'' js'' p''

tweakOrn : ∀ {I J} {e : J → I} {D E} (O : Orn e D E) → Orn (und ∘ proj₂) E ⌊ algOrn D (ornAlg O) ⌋
tweakOrn {e = e} {D} (wrap O) =
  wrap λ { {._} (ok (i , j)) → Δ[ js ∶ ⟦ D at i ⟧ (_⁻¹_ e) ] Δ[ p ∶ ornProp (O j) js ] tweakOrn-aux (O j) js p }

ft-existence-aux : ∀ {I J} {e : J → I} {D' E'} (O' : ROrn e D' E') {X} (xs : ⟦ E' ⟧ X) →
                   Σ[ js ∶ ⟦ D' ⟧ (_⁻¹_ e) ] ⟦ OptPRD (Δ (ornProp O' js) (tweakOrn-aux O' js)) xs ⟧ (const ⊤)
ft-existence-aux ∎            xs                                      = tt , tt , tt
ft-existence-aux (ṿ {j} refl) xs                                      = ok j , refl , tt
ft-existence-aux (σ S O')     (s , xs)   with ft-existence-aux (O' s) xs
ft-existence-aux (σ S O')     (s , xs)   | js , p , q                 = (s , js) , p , refl , q
ft-existence-aux (Δ T O')     (t , xs)   with ft-existence-aux (O' t) xs
ft-existence-aux (Δ T O')     (t , xs)   | js , p , q                 = js , (t , p) , refl , q
ft-existence-aux (∇ s O')     xs         with ft-existence-aux O' xs
ft-existence-aux (∇ s O')     xs         | js , p , q                 = (s , js) , (refl , p) , q
ft-existence-aux (O' * O'')   (xs , xs') with ft-existence-aux O' xs | ft-existence-aux O'' xs'
ft-existence-aux (O' * O'')   (xs , xs') | js , p , q | js' , p' , q' = (js , js') , (p , p') , (q , q')

ft-existence : ∀ {I J} {e : J → I} {D E} (O : Orn e D E) →
               ∀ {j} (ij : (und ∘ proj₂) ⁻¹ j) {X} (xs : Ḟ E X j) → ⟦ OptPRD (Orn.comp (tweakOrn O) ij) xs ⟧ (const ⊤)
ft-existence {e = e} (wrap O) (ok (.(e j) , ok j)) xs = ft-existence-aux (O (ok j)) xs

ft-existence-unique :
  ∀ {I J} {e : J → I} {D E} (O : Orn e D E) → ∀ {j} (ij : (und ∘ proj₂) ⁻¹ j) {X} (xs : Ḟ E X j) → Unique (≡-Setoid _) (ft-existence O ij xs)
ft-existence-unique {I} {J} {e = e} (wrap O) (ok (.(e j) , ok j)) {X} = aux (O (ok j))
  where
    aux : ∀ {D' E'} (O' : ROrn e D' E') (xs : ⟦ E' ⟧ X) → Unique (≡-Setoid _) (ft-existence-aux O' xs)
    aux ∎          xs         ys                                                = refl
    aux (ṿ idx)    xs         (ok j , refl , q)                   with idx
    aux (ṿ idx)    xs         (ok j , refl , q)                   | refl        = refl
    aux (σ S O')   (s , xs)   ((.s , js) , p , refl , q)          with aux (O' s) xs (js , p , q)
    aux (σ S O')   (s , xs)   ((.s , ._) , ._ , refl , ._)        | refl        = refl
    aux (Δ T O')   (t , xs)   (js , (.t , p) , refl , q)          with aux (O' t) xs (js , p , q)
    aux (Δ T O')   (t , xs)   (._ , (.t , ._) , refl , ._)        | refl        = refl
    aux (∇ s O')   xs         ((.s , js) , (refl , p) , q)        with aux O' xs (js , p , q)
    aux (∇ s O')   xs         ((.s , ._) , (refl , ._) , ._)      | refl        = refl
    aux (O' * O'') (xs , xs') ((js , js') , (p , p') , (q , q'))  with aux O' xs (js , p , q) | aux O'' xs' (js' , p' , q')
    aux (O' * O'') (xs , xs') ((._ , ._) , (._ , ._) , (._ , ._)) | refl | refl = refl

AOOA-theorem : ∀ {I J} {e : J → I} {D E} → (O : Orn e D E) → IsoOrn (tweakOrn O)
AOOA-theorem {e = e} O =
  (record { to = λ j → e j , ok j; from = und ∘ proj₂; to-from-inverse = λ { (.(e j) , ok j) → refl }; from-to-inverse = frefl } , refl) ,
  ft-existence O , ft-existence-unique O
