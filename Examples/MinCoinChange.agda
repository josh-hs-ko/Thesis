-- Solving the minimum coin change problem with the greedy theorem and algebraic ornamentation.

module Thesis.Examples.MinCoinChange where

open import Thesis.Prelude.Function
open import Thesis.Prelude.InverseImage
open import Thesis.Prelude.Function.Fam
open import Thesis.Prelude.Preorder
open import Thesis.Description hiding (_*_)
open import Thesis.Ornament hiding (_*_)
open import Thesis.Ornament.SequentialComposition
open import Thesis.Relation
open import Thesis.Examples.Nat hiding (_+_)
open import Thesis.Examples.List
open import Thesis.Examples.List.Sorted

open import Function using (id; const; _∘_; flip; _on_)
open import Data.Unit using (⊤; tt)
open import Data.Bool using (Bool; false; true)
open import Data.Nat using (ℕ; _+_; _*_) renaming (_≤_ to _≤ℕ_; _<_ to _<ℕ_; decTotalOrder to ℕ-DecTotalOrder)
open import Data.Nat.Properties renaming (<-trans to <ℕ-trans)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_; uncurry) renaming (map to _**_)
open import Relation.Binary using (module DecTotalOrder)
import Relation.Binary.PreorderReasoning as PreorderReasoning
open import Relation.Binary.PropositionalEquality using (_≡_; refl)


--------
-- coins

data Coin : Set where
  1p : Coin
  2p : Coin
  5p : Coin
  ∞p : Coin

value : Coin → ℕ
value 1p = 1
value 2p = 2
value 5p = 5
value ∞p = 999

_<_ : Coin → Coin → Set
_<_ = _<ℕ_ on value


--------
-- coin bags as sorted association lists

CoinSListOD : OrnDesc Coin ! ⌊ ListOD Coin ⌋
CoinSListOD = SListOD Coin (flip _<_) (flip <ℕ-trans)

CoinBagOD : OrnDesc Coin id ⌊ CoinSListOD ⌋
CoinBagOD = wrap λ { {._} (ok c) →
                  σ Bool λ { false → ∎
                           ; true → σ[ d ∶ Coin ] Δ[ n ∶ ℕ ] σ (d < c) λ _ → ṿ (ok d) } }

CoinBag : Coin → Set
CoinBag = μ ⌊ CoinBagOD ⌋

total-value-alg : Ḟ ⌊ CoinBagOD ⌋ (const ℕ) ⇉ (const ℕ)
total-value-alg (false , _            ) = 0
total-value-alg (true  , c , n , _ , m) = n * value c + m

total-value : ∀ {c} → CoinBag c → ℕ
total-value = fold total-value-alg

lengthCB : ∀ {c} → CoinBag c → ℕ
lengthCB = toℕ ∘ length ∘ forget (⌈ CoinSListOD ⌉ ⊙ ⌈ CoinBagOD ⌉)


{-

--------
-- specification

R : CoinBag ↝ CoinBag
R = wrap (flip _≤ℕ_ on lengthCB)

R-transitive : R • R ⊆ R
R-transitive = wrap λ b → wrap λ { b' (b'' , b≥b'' , b''≥b') → DecTotalOrder.trans ℕ-DecTotalOrder b''≥b' b≥b'' }

{-

unbounded : CoinBag ↝ CoinBag
unbounded = (λ c _ → c ≡ ∞p) ¿

unbounded-transitive : unbounded • unbounded ⊆ unbounded
unbounded-transitive =
  begin
    unbounded • unbounded
      ⊆⟨ •-monotonic-r unbounded (coreflexive (λ c _ → c ≡ ∞p)) ⟩
    idR • unbounded
      ⊆⟨ proj₁ (idR-l unbounded) ⟩
    unbounded
  □
  where open PreorderReasoning (⊆-Preorder CoinBag CoinBag) renaming (_∼⟨_⟩_ to _⊆⟨_⟩_; _∎ to _□)

R : CoinBag ↝ CoinBag
R = leq ∩ unbounded

R-transitive : R • R ⊆ R
R-transitive =
  (begin
     R • R ⊆ R
       ⇐⟨ uncurry ∩-universal-⇐ ⟩
     ((R • R ⊆ leq) × (R • R ⊆ unbounded))
       ⇐⟨ (let (p , q) = ∩-universal-⇒ ⊆-refl in ⊆-trans (•-monotonic p p) ** ⊆-trans (•-monotonic q q)) ⟩
     ((leq • leq ⊆ leq) × (unbounded • unbounded ⊆ unbounded))
   □) (leq-transitive , unbounded-transitive)
  where open PreorderReasoning (⇐-Preorder) renaming (_∼⟨_⟩_ to _⇐⟨_⟩_; _∎ to _□)

-}

S : Ḟ ⌊ CoinBagOD ⌋ (const ℕ) ↝ (const ℕ)
S = fun total-value-alg

monotonicity : α • Ṙ ⌊ CoinBagOD ⌋ R • α º ⊆ R
monotonicity = {!!}

Q : CBag ↝ CBag

-}
