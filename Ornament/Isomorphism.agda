-- A sufficient condition for establishing an isomorphism between the two types related by a ornament.

module Ornament.Isomorphism where

open import Prelude.Equality
open import Prelude.Function
open import Prelude.Category
import Prelude.Category.Isomorphism as Isomorphism; open Isomorphism Fun
open import Prelude.InverseImage
open import Prelude.Product
open import Refinement
open import Refinement.Isomorphism
open import Description
open import Ornament
open import Ornament.ParallelComposition
open import Ornament.RefinementSemantics

open import Function using (id; const; _∘_)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; cong; cong₂) renaming (setoid to ≡-Setoid)


IsoOrn : ∀ {I J} {e : J → I} {D E} → Orn e D E → Set₁
IsoOrn {I} {J} {e} {D} {E} O =
  PartOfIso e ×
  (Σ[ existence ∶ (∀ {i} (j : e ⁻¹ i) {X} (xs : Ḟ D X i) → ⟦ OptPRD (Orn.comp O j) xs ⟧ (const ⊤)) ]
     (∀ {i} (j : e ⁻¹ i) {X} (xs : Ḟ D X i) → Unique (≡-Setoid _) (existence j xs)))

module PromotionProof {I J : Set} {e : J → I} {D E} (O : Orn e D E) (iso-O : IsoOrn O) where

  mutual
  
    induce-promotion-proof : ∀ {i} (x : μ D i) → (j : e ⁻¹ i) → OptP O j x
    induce-promotion-proof = induction D (λ {i} x → (j : e ⁻¹ i) → OptP O j x) induce-promotion-proof-alg

    induce-promotion-proof-alg :
      {i : I} (xs : Ḟ D (μ D) i) → All (D at i) (λ {i} x → (j : e ⁻¹ i) → OptP O j x) xs →
      (j : e ⁻¹ i) → OptP O j (con xs)
    induce-promotion-proof-alg xs all j = con (induce-promotion-proof-aux (Orn.comp O j) xs all (proj₁ (proj₂ iso-O) j xs))

    induce-promotion-proof-aux :
      ∀ {D' E'} (O' : ROrn e D' E') (xs : ⟦ D' ⟧ (μ D)) → All D' (λ {i} x → (j : e ⁻¹ i) → OptP O j x) xs →
      ⟦ OptPRD O' xs ⟧ (const ⊤) → ⟦ toRDesc (pcROrn O' (toROrn (erode D' xs))) ⟧ (μ (OptPD O))
    induce-promotion-proof-aux ∎            xs         all          hs          = tt
    induce-promotion-proof-aux (ṿ {j} refl) xs         all          hs          = all (ok j)
    induce-promotion-proof-aux (σ S O')     (s , xs)   all          hs          = induce-promotion-proof-aux (O' s) xs all hs
    induce-promotion-proof-aux (Δ T O')     xs         all          (t , hs)    = t , induce-promotion-proof-aux (O' t) xs all hs
    induce-promotion-proof-aux (∇ s O')     (.s , xs)  all          (refl , hs) = refl , induce-promotion-proof-aux O' xs all hs
    induce-promotion-proof-aux (O' * O'')   (xs , xs') (all , all') (hs , hs')  = induce-promotion-proof-aux O' xs all hs ,
                                                                                  induce-promotion-proof-aux O'' xs' all' hs'

  induce-uniqueness : ∀ {i} (x : μ D i) → (j : e ⁻¹ i) → Unique (≡-Setoid _) (induce-promotion-proof x j)
  induce-uniqueness =
    induction D (λ {i} x → (j : e ⁻¹ i) → Unique (≡-Setoid _) (induce-promotion-proof x j))
      λ { xs all j (con ps) → cong con (aux (Orn.comp O j) xs all (proj₁ (proj₂ iso-O) j xs) (proj₂ (proj₂ iso-O) j xs) ps) }
    where
      aux : ∀ {D' E'} (O' : ROrn e D' E')
            (xs : ⟦ D' ⟧ (μ D)) (all : All D' (λ {i} x → (j : e ⁻¹ i) → Unique (≡-Setoid _) (induce-promotion-proof x j)) xs)
            (ts : ⟦ OptPRD O' xs ⟧ (const ⊤)) → Unique (≡-Setoid _) ts →
            Unique (≡-Setoid _) (induce-promotion-proof-aux O' xs
                                   (everywhereInduction D D' (λ {i} x → (j : e ⁻¹ i) → OptP O j x) induce-promotion-proof-alg xs) ts)
      aux ∎            xs         all          ts          ts-unique ps          = refl
      aux (ṿ {j} refl) xs         all          ts          ts-unique ps          = all (ok j) ps
      aux (σ S O')     (s , xs)   all          ts          ts-unique ps          = aux (O' s) xs all ts ts-unique ps
      aux (Δ T O')     xs         all          (t , ts)    ts-unique (t' , ps)
        with cong proj₁ (ts-unique (t' , remove-recursive-objects (OptPRD (O' t') xs) ps))
      aux (Δ T O')     xs         all          (t , ts)    ts-unique (.t , ps)
        | refl = cong (_,_ t) (aux (O' t) xs all ts (λ ts' → cong-proj₂ (ts-unique (t , ts'))) ps)
      aux (∇ s O')     (.s , xs)  all          (refl , ts) ts-unique (refl , ps) =
        cong (_,_ refl) (aux O' xs all ts (λ ts' → cong-proj₂ (ts-unique (refl , ts'))) ps)
      aux (O' * O'')   (xs , xs') (all , all') (ts , ts')  ts-unique (ps , ps')  =
        cong₂ _,_ (aux O' xs all ts (λ ts'' → cong proj₁ (ts-unique (ts'' , ts'))) ps)
                  (aux O'' xs' all' ts' (λ ts'' → cong-proj₂ (ts-unique (ts , ts''))) ps')

RSemIso : ∀ {I J} {e : J → I} {D E} (O : Orn e D E) → IsoOrn O → IsoFRefinement (RSem' O)
RSemIso {I} {J} {e} O iso-O =
  proj₁ iso-O , λ j → (λ x → PromotionProof.induce-promotion-proof O iso-O x j) , (λ x → PromotionProof.induce-uniqueness O iso-O x j)
