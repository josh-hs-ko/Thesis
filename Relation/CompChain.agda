-- Combinators that help avoiding explicit applications of monotonicity and associativity of relational composition
-- and preservation of composition by relators and converse.

module Relation.CompChain where

open import Description
open import Relation

import Relation.Binary.PreorderReasoning as PreorderReasoning
open import Data.Product using (Σ; _,_; proj₁; proj₂)


infix 2 _◇
infixr 1 _▪_

data CompChain {I : Set} : (I → Set) → (I → Set) → Set₁ where
  _◇  : ∀ {X Y} → X ↝ Y → CompChain X Y
  _▪_ : ∀ {X Y Z} → Y ↝ Z → CompChain X Y → CompChain X Z

collapse : {I : Set} {X Y : I → Set} → CompChain X Y → X ↝ Y
collapse (R    ◇) = R
collapse (R ▪ Rs) = R • collapse Rs

comp : {I : Set} {X Y Z : I → Set} → CompChain Y Z → X ↝ Y → X ↝ Z
comp (R    ◇) S = R • S
comp (R ▪ Rs) S = R • comp Rs S

comp-collapse-lemma : {I : Set} {X Y Z : I → Set} → (Rs : CompChain Y Z) (S : X ↝ Y) → comp Rs S ≃ collapse Rs • S
comp-collapse-lemma (R    ◇) S = ≃-refl
comp-collapse-lemma (R ▪ Rs) S = ≃-trans (•-cong-l R (comp-collapse-lemma Rs S)) (≃-sym (•-assoc R (collapse Rs) S))

⊆-chain-l : {I : Set} {X Y Z : I → Set} → (Rs : CompChain Y Z) → {S T : X ↝ Y} → S ⊆ T → comp Rs S ⊆ comp Rs T
⊆-chain-l (R    ◇) S⊆T = •-monotonic-l R S⊆T
⊆-chain-l (R ▪ Rs) S⊆T = •-monotonic-l R (⊆-chain-l Rs S⊆T)

⊆-chain-r : {I : Set} {X Y Z : I → Set} → (Rs Ss : CompChain Y Z) →
             collapse Rs ⊆ collapse Ss → {T : X ↝ Y} → comp Rs T ⊆ comp Ss T
⊆-chain-r {I} {X} {Y} {Z} Rs Ss Rs⊆Ss {T} =
  begin
    comp Rs T
      ⊆⟨ proj₁ (comp-collapse-lemma Rs T) ⟩
    collapse Rs • T
      ⊆⟨ •-monotonic-r T Rs⊆Ss ⟩
    collapse Ss • T
      ⊆⟨ proj₂ (comp-collapse-lemma Ss T) ⟩
    comp Ss T
  □
  where open PreorderReasoning (⊆-Preorder X Z) renaming (_∼⟨_⟩_ to _⊆⟨_⟩_; _∎ to _□)

⊆-chain : {I : Set} {X Y Z W : I → Set} (Rs : CompChain Z W) (Ss Ts : CompChain Y Z) →
           collapse Ss ⊆ collapse Ts → {U : X ↝ Y} → comp Rs (comp Ss U) ⊆ comp Rs (comp Ts U)
⊆-chain Rs Ss Ts Ss⊆Ts = ⊆-chain-l Rs (⊆-chain-r Ss Ts Ss⊆Ts)

⊇-chain-l : {I : Set} {X Y Z : I → Set} → (Rs : CompChain Y Z) → {S T : X ↝ Y} → S ⊇ T → comp Rs S ⊇ comp Rs T
⊇-chain-l Rs S⊇T = ⊆-chain-l Rs S⊇T

⊇-chain-r : {I : Set} {X Y Z : I → Set} → (Rs Ss : CompChain Y Z) →
             collapse Rs ⊇ collapse Ss → {T : X ↝ Y} → comp Rs T ⊇ comp Ss T
⊇-chain-r Rs Ss Rs⊇Ss = ⊆-chain-r Ss Rs Rs⊇Ss

⊇-chain : {I : Set} {X Y Z W : I → Set} (Rs : CompChain Z W) (Ss Ts : CompChain Y Z) →
           collapse Ss ⊇ collapse Ts → {U : X ↝ Y} → comp Rs (comp Ss U) ⊇ comp Rs (comp Ts U)
⊇-chain Rs Ss Ts Ss⊇Ts = ⊆-chain Rs Ts Ss Ss⊇Ts

≃-chain-l : {I : Set} {X Y Z : I → Set} → (Rs : CompChain Y Z) → {S T : X ↝ Y} → S ≃ T → comp Rs S ≃ comp Rs T
≃-chain-l Rs (S⊆T , S⊇T) = ⊆-chain-l Rs S⊆T , ⊆-chain-l Rs S⊇T

≃-chain-r : {I : Set} {X Y Z : I → Set} → (Rs Ss : CompChain Y Z) →
             collapse Rs ≃ collapse Ss → {T : X ↝ Y} → comp Rs T ≃ comp Ss T
≃-chain-r Rs Ss (Rs⊆Ss , Rs⊇Ss) = ⊆-chain-r Rs Ss Rs⊆Ss , ⊆-chain-r Ss Rs Rs⊇Ss

≃-chain : {I : Set} {X Y Z W : I → Set} (Rs : CompChain Z W) (Ss Ts : CompChain Y Z) →
           collapse Ss ≃ collapse Ts → {U : X ↝ Y} → comp Rs (comp Ss U) ≃ comp Rs (comp Ts U)
≃-chain Rs Ss Ts Ss≃Ts = ≃-chain-l Rs (≃-chain-r Ss Ts Ss≃Ts)

mapChain-Ṙ : {I : Set} (D : Desc I) {X Y : I → Set} → CompChain X Y → CompChain (Ḟ D X) (Ḟ D Y)
mapChain-Ṙ D (R    ◇) = Ṙ D R ◇
mapChain-Ṙ D (R ▪ Rs) = Ṙ D R ▪ mapChain-Ṙ D Rs

Ṙ-chain : {I : Set} (D : Desc I) {X Y : I → Set} (Rs : CompChain X Y) → Ṙ D (collapse Rs) ≃ collapse (mapChain-Ṙ D Rs)
Ṙ-chain D (R    ◇) = ≃-refl
Ṙ-chain D (R ▪ Rs) = ≃-trans (Ṙ-preserves-comp D R (collapse Rs)) (•-cong-l (Ṙ D R) (Ṙ-chain D Rs))

snocChain : {I : Set} {X Y Z : I → Set} → CompChain Y Z → X ↝ Y → CompChain X Z
snocChain (R    ◇) S = R ▪ S ◇
snocChain (R ▪ Rs) S = R ▪ snocChain Rs S

collapse-snocChain-lemma :
  {I : Set} {X Y Z : I → Set} (Rs : CompChain Y Z) (S : X ↝ Y) → collapse (snocChain Rs S) ≃ collapse Rs • S
collapse-snocChain-lemma (R    ◇) S = ≃-refl
collapse-snocChain-lemma (R ▪ Rs) S = ≃-trans (•-cong-l R (collapse-snocChain-lemma Rs S)) (≃-sym (•-assoc R (collapse Rs) S))

mapChain-º : {I : Set} {X Y : I → Set} → CompChain X Y → CompChain Y X
mapChain-º (R    ◇) = R º ◇
mapChain-º (R ▪ Rs) = snocChain (mapChain-º Rs) (R º)

º-chain : {I : Set} {X Y : I → Set} (Rs : CompChain X Y) → (collapse Rs) º ≃ collapse (mapChain-º Rs)
º-chain (R    ◇) = ≃-refl
º-chain (R ▪ Rs) = ≃-trans (º-preserves-comp R (collapse Rs))
                             (≃-trans (•-cong-r (R º) (º-chain Rs)) (≃-sym (collapse-snocChain-lemma (mapChain-º Rs) (R º))))

data CompTree {I : Set} : (I → Set) → (I → Set) → Set₁ where
  [_]  : ∀ {X Y} → X ↝ Y → CompTree X Y
  _▪_ : ∀ {X Y Z} → CompTree Y Z → CompTree X Y → CompTree X Z

collapseTree : {I : Set} {X Y : I → Set} → CompTree X Y → X ↝ Y
collapseTree [ R ] = R
collapseTree (Rs ▪ Ss) = collapseTree Rs • collapseTree Ss

appendChain : {I : Set} {X Y Z : I → Set} → CompChain Y Z → CompChain X Y → CompChain X Z
appendChain (R    ◇) Ss = R ▪ Ss
appendChain (R ▪ Rs) Ss = R ▪ appendChain Rs Ss

toChain : {I : Set} {X Y : I → Set} → CompTree X Y → CompChain X Y
toChain [ R ]     = R ◇
toChain (Rs ▪ Ss) = appendChain (toChain Rs) (toChain Ss)

collapse-appendChain-lemma :
  {I : Set} {X Y Z : I → Set} (Rs : CompChain Y Z) (Ss : CompChain X Y) → collapse (appendChain Rs Ss) ≃ collapse Rs • collapse Ss
collapse-appendChain-lemma (R    ◇) Ss = ≃-refl
collapse-appendChain-lemma (R ▪ Rs) Ss =
  ≃-trans (•-cong-l R (collapse-appendChain-lemma Rs Ss)) (≃-sym (•-assoc R (collapse Rs) (collapse Ss)))

chain-normalise : {I : Set} {X Y : I → Set} (Rs : CompTree X Y) → collapseTree Rs ≃ collapse (toChain Rs)
chain-normalise [ R ]     = ≃-refl
chain-normalise (Rs ▪ Ss) =
  ≃-trans (•-cong (chain-normalise Rs) (chain-normalise Ss)) (≃-sym (collapse-appendChain-lemma (toChain Rs) (toChain Ss)))
