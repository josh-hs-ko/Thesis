-- Let `D : Desc I` be a description.
-- The category `RAlg' D` is the wide subcategory of the category of relational `D`-algebras where the morphisms are restricted to be functions.

open import Description

module Relation.AlgCategory {I : Set} (D : Desc I) where

{-

open import Prelude.Equality
open import Prelude.Category
open import Prelude.Function
open import Prelude.Function.Fam
open import Relation
open import Relation.CompChain

open import Function using (id; _∘_)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
import Relation.Binary.PreorderReasoning as PreorderReasoning

record RAlgebra : Set₁ where
  constructor _,_
  field
    Carrier : I → Set
    R       : Ḟ D Carrier ↝⁺ Carrier

record RAlg'Morphism (R S : RAlgebra) : Set₁ where
  constructor _,_
  field
    h : RAlgebra.Carrier R ⇉ RAlgebra.Carrier S
    c : fun⁺ h •⁺ RAlgebra.R R ⊆⁺ RAlgebra.R S •⁺ Ṙ D (fun⁺ h)

RAlg'Morphism-id : {R : RAlgebra} → RAlg'Morphism R R
RAlg'Morphism-id {X , R} =
  id , (begin
          idR⁺ •⁺ R
            ⊆⁺⟨ proj₁ (idR⁺-l R) ⟩
          R
            ⊆⁺⟨ proj₂ (idR⁺-r R) ⟩
          R •⁺ idR⁺
            ⊆⁺⟨ •⁺-monotonic-l R (proj₂ (Ṙ-preserves-idR⁺ D)) ⟩
          R •⁺ Ṙ D idR⁺
        ∎)
  where open PreorderReasoning (⊆⁺-Preorder (Ḟ D X) X) renaming (_∼⟨_⟩_ to _⊆⁺⟨_⟩_)

RAlg'Morphism-comp : {R S T : RAlgebra} → RAlg'Morphism S T → RAlg'Morphism R S → RAlg'Morphism R T
RAlg'Morphism-comp {X , R} {Y , S} {Z , T} (h , ch) (g , cg) =
  h ∘ g , (begin
             fun⁺ (h ∘ g) •⁺ R
               ⊆⁺⟨ ⊆⁺-chain-r (fun⁺ (h ∘ g) ◇⁺) (fun⁺ h ▪⁺ fun⁺ g ◇⁺) (proj₁ (fun⁺-preserves-comp h g)) ⟩
             fun⁺ h •⁺ fun⁺ g •⁺ R
               ⊆⁺⟨ •⁺-monotonic-l (fun⁺ h) cg ⟩
             fun⁺ h •⁺ S •⁺ Ṙ D (fun⁺ g)
               ⊆⁺⟨ ⊆⁺-chain-r (fun⁺ h ▪⁺ S ◇⁺) (T ▪⁺ Ṙ D (fun⁺ h) ◇⁺) ch ⟩
             T •⁺ Ṙ D (fun⁺ h) •⁺ Ṙ D (fun⁺ g)
               ⊆⁺⟨ •⁺-monotonic-l T (proj₂ (Ṙ-preserves-comp D (fun⁺ h) (fun⁺ g))) ⟩
             T •⁺ Ṙ D (fun⁺ h •⁺ fun⁺ g)
               ⊆⁺⟨ •⁺-monotonic-l T (Ṙ-monotonic D (proj₂ (fun⁺-preserves-comp h g))) ⟩
             T •⁺ Ṙ D (fun⁺ (h ∘ g))
           ∎)
  where open PreorderReasoning (⊆⁺-Preorder (Ḟ D X) Z) renaming (_∼⟨_⟩_ to _⊆⁺⟨_⟩_)

RAlg' : Category
RAlg' =
  record { Object   = RAlgebra
         ; Morphism = λ R S → toSetoid (ProductSetoid (⇉-Setoid (RAlgebra.Carrier R) (RAlgebra.Carrier S)) {!⊆⁺-Setoid !}) {!!}
         ; _·_ = RAlg'Morphism-comp
         ; id  = RAlg'Morphism-id
         ; id-l   = {!!}
         ; id-r   = {!!}
         ; assoc  = {!!}
         ; cong-l = {!!}
         ; cong-r = {!!} }

-}
