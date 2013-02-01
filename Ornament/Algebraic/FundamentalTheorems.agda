-- Two fundamental theorems about algebraic ornaments and ornamental algebras.
-- *The AOOA Theorem:* Algebraic ornamentation by an ornamental algebra produces an isomorphic datatype.
-- *The OAAO Theorem:* An ornamental algebra derived from an algebraic ornament is isomorphic to the algebra of the ornament.

module Thesis.Ornament.Algebraic.FundamentalTheorems where

open import Thesis.Prelude.Equality
open import Thesis.Prelude.Category.Isomorphism
open import Thesis.Prelude.Function
open import Thesis.Prelude.Function.Fam
open import Thesis.Prelude.Product
open import Thesis.Prelude.InverseImage
open import Thesis.Description
open import Thesis.Ornament
open import Thesis.Ornament.RefinementSemantics
open import Thesis.Ornament.Isomorphism
open import Thesis.Ornament.Algebraic
open import Thesis.Relation
open import Thesis.Relation.Fold

open import Function using (const; _∘_)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂) renaming (setoid to ≡-Setoid)


--------
-- algebraic ornamentation by an ornamental algebra produces an isomorphic datatype

tweakOrn-aux :
  ∀ {I J} {e : J → I} {D' : RDesc I} {E' : RDesc J} →
  (O' : ROrn e D' E') → (ds : ⟦ D' ⟧ (_⁻¹_ e)) → ornProp O' ds → ROrn (und ∘ proj₂) E' (toRDesc (erode D' ds))
tweakOrn-aux ∎          ds           p          = ∎
tweakOrn-aux (ṿ idx)    j'           eq         = ṿ eq
tweakOrn-aux (σ S O')   (s , ds)     p          = ∇ s (tweakOrn-aux (O' s) ds p)
tweakOrn-aux (Δ T O')   ds           (t , p)    = ∇ t (tweakOrn-aux (O' t) ds p)
tweakOrn-aux (∇ s O')   (.s , ds)    (refl , p) = tweakOrn-aux O' ds p
tweakOrn-aux (O' * O'') (ds' , ds'') (p' , p'') = tweakOrn-aux O' ds' p' * tweakOrn-aux O'' ds'' p''

tweakOrn : ∀ {I J} {e : J → I} {D E} → (O : Orn e D E) → Orn (und ∘ proj₂) E ⌊ algOrn D (ornAlg O) ⌋
tweakOrn {I} {J} {e} {D} {E} (wrap O) =
  wrap λ { {._} (ok (i , j)) → Δ[ ds ∶ ⟦ D at i ⟧ (_⁻¹_ e) ] Δ[ p ∶ ornProp (O j) ds ] tweakOrn-aux (O j) ds p }

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
  record { from = λ j → e j , ok j; to-from-inverse = frefl; from-to-inverse = λ { (.(e j) , ok j) → refl } } ,
  ft-existence O , ft-existence-unique O


--------
-- ornamental algebra derived from an algebraic ornament is isomorphic to the algebra of the ornament

module OAAO {I : Set} {J : I → Set} (D : Desc I) (R : Ḟ D J ↝⁺ J) where

  h : J ⇉ _⁻¹_ proj₁
  h {i} = ok ∘ _,_ i

  OAAO-theorem-aux-computation : (D : RDesc I) (js : ⟦ D ⟧ J) → ornProp (toROrn (erode D js)) (mapF D h js)
  OAAO-theorem-aux-computation ∎       js         = tt
  OAAO-theorem-aux-computation (ṿ i)   j          = refl
  OAAO-theorem-aux-computation (σ S D) (s , js)   = refl , OAAO-theorem-aux-computation (D s) js
  OAAO-theorem-aux-computation (D * E) (js , js') = OAAO-theorem-aux-computation D js , OAAO-theorem-aux-computation E js'

  OAAO-theorem-aux-unique : (D : RDesc I) (js js' : ⟦ D ⟧ J) → ornProp (toROrn (erode D js')) (mapF D h js) → js ≡ js'
  OAAO-theorem-aux-unique ∎       js        js'         p          = refl
  OAAO-theorem-aux-unique (ṿ i)   j         j'          p          = cong-proj₂ p
  OAAO-theorem-aux-unique (σ S D) (s , js)  (.s , js')  (refl , p) = cong (_,_ s) (OAAO-theorem-aux-unique (D s) js js' p)
  OAAO-theorem-aux-unique (D * E) (js , ks) (js' , ks') (p , p')   = cong₂ _,_ (OAAO-theorem-aux-unique D js js' p)
                                                                               (OAAO-theorem-aux-unique E ks ks' p')

  OAAO-theorem : fun⁺ h •⁺ R ≃⁺ ornAlg ⌈ algOrn D R ⌉ •⁺ Ṙ D (fun⁺ h)
  OAAO-theorem =
    wrap (λ i → wrap λ { js ._ (j , r , refl) →
                         Ḟ-map D h js , mapR-fun-computation (D at i) h js , js , r , OAAO-theorem-aux-computation (D at i) js }) ,
    wrap (λ i → wrap λ { js ij (ijs , rs , q) → aux js ij ijs rs q })
    where
      aux : ∀ {i} (js : Ḟ D J i) (ij : proj₁ {B = J} ⁻¹ i) (ijs : Ḟ D (_⁻¹_ proj₁) i) (rs : mapR (D at i) (fun⁺ h) js ijs) →
            (q : (ornAlg ⌈ algOrn D R ⌉ !!) i ijs ij) → ((fun⁺ h •⁺ R) !!) i js ij
      aux js (ok (i , j)) ijs rs (js' , r , p) with mapR-fun-unique (D at i) h js ijs rs
      aux js (ok (i , j)) ._  rs (js' , r , p) | refl with OAAO-theorem-aux-unique (D at i) js js' p
      aux js (ok (i , j)) ._  rs (.js , r , p) | refl | refl = j , r , refl

  g : _⁻¹_ proj₁ ⇉ J
  g (ok (i , j)) = j

  hg-inverse : ∀ {i} (ij : proj₁ ⁻¹ i) → h (g ij) ≡ ij
  hg-inverse (ok (i , j)) = refl

  hg-iso : ∀ i → Iso Fun (J i) (proj₁ {B = J} ⁻¹ i)
  hg-iso i = record { to = h; from = g; to-from-inverse = hg-inverse; from-to-inverse = frefl }
