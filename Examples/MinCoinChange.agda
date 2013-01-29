-- Solving the minimum coin change problem with the greedy theorem and algebraic ornamentation.

module Thesis.Examples.MinCoinChange where

open import Thesis.Prelude.Function
open import Thesis.Prelude.InverseImage
open import Thesis.Prelude.Function.Fam
open import Thesis.Prelude.Implication
open import Thesis.Description hiding (_*_)
open import Thesis.Ornament hiding (_*_)
open import Thesis.Ornament.SequentialComposition
open import Thesis.Relation
open import Thesis.Relation.Meet
open import Thesis.Examples.Nat hiding (_+_)
open import Thesis.Examples.List
open import Thesis.Examples.List.Sorted

open import Function using (id; const; _∘_; flip; _on_)
open import Data.Unit using (⊤; tt)
open import Data.Bool using (Bool; false; true)
open import Data.Nat using (ℕ; _+_; _*_) renaming (_≤_ to _≤ℕ_; _<_ to _<ℕ_)
open import Data.Nat.Properties renaming (<-trans to <ℕ-trans)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
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

CListOD : OrnDesc Coin ! ⌊ ListOD Coin ⌋
CListOD = SListOD Coin (flip _<_) (flip <ℕ-trans)

CBagOD : OrnDesc Coin id ⌊ CListOD ⌋
CBagOD = wrap λ { {._} (ok c) →
                  σ Bool λ { false → ∎
                           ; true → σ[ d ∶ Coin ] Δ[ n ∶ ℕ ] σ (d < c) λ _ → ṿ (ok d) } }

CBag : Coin → Set
CBag = μ ⌊ CBagOD ⌋

total-value-alg : Ḟ ⌊ CBagOD ⌋ (const ℕ) ⇒ (const ℕ)
total-value-alg (false , _            ) = 0
total-value-alg (true  , c , n , _ , m) = n * value c + m

total-value : ∀ {c} → CBag c → ℕ
total-value = fold total-value-alg

lengthCB : ∀ {c} → CBag c → ℕ
lengthCB = toℕ ∘ length ∘ forget (⌈ CListOD ⌉ ⊙ ⌈ CBagOD ⌉)


--------
-- specification

leq : CBag ↝ CBag
leq = wrap (flip _≤ℕ_ on lengthCB)

unbounded : CBag ↝ CBag
unbounded = (λ c _ → c ≡ ∞p) ¿

R : CBag ↝ CBag
R = leq ∩ unbounded

S : Ḟ ⌊ CBagOD ⌋ (const ℕ) ↝ (const ℕ)
S = fun total-value-alg

R-transitive : R • R ⊆ R
R-transitive =
  (begin
    R • R ⊆ R
      ⇐⟨ {!!} ⟩
    ((R • R ⊆ leq) × (R • R ⊆ unbounded))
      ⇐⟨ {!!} ⟩
    ((leq • leq ⊆ leq) × (unbounded • unbounded ⊆ unbounded))
   □) ({!!} , {!!})
  where open PreorderReasoning (⇐-Preorder) renaming (_∼⟨_⟩_ to _⇐⟨_⟩_; _∎ to _□)