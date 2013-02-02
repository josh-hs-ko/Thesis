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
open import Thesis.Relation.CompChain
open import Thesis.Relation.Fold
open import Thesis.Relation.GreedyTheorem
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
value ∞p = 42

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
lengthCB = toℕ ∘ forget (⌈ ListOD Coin ⌉ ⊙ (⌈ CoinSListOD ⌉ ⊙ ⌈ CoinBagOD ⌉))


--------
-- specification

leq-ℕ : const {B = Coin} ℕ ↝⁺ const ℕ
leq-ℕ = wrap (const (flip _≤ℕ_))

leq-ℕ-transitive : leq-ℕ •⁺ leq-ℕ ⊆⁺ leq-ℕ
leq-ℕ-transitive = wrap (const (wrap λ { x y (z , z≤x , y≤z) → DecTotalOrder.trans ℕ-DecTotalOrder y≤z z≤x }))

R : CoinBag ↝⁺ CoinBag
R = fun⁺ lengthCB º⁺ •⁺ leq-ℕ •⁺ fun⁺ lengthCB

R-transitive : R •⁺ R ⊆⁺ R
R-transitive =
  begin
    (fun⁺ lengthCB º⁺ •⁺ leq-ℕ •⁺ fun⁺ lengthCB) •⁺ (fun⁺ lengthCB º⁺ •⁺ leq-ℕ •⁺ fun⁺ lengthCB)
      ⊆⁺⟨ proj₁ (chain-normalise⁺
                  (([ fun⁺ lengthCB º⁺ ]⁺ ▪⁺ [ leq-ℕ ]⁺ ▪⁺ [ fun⁺ lengthCB ]⁺) ▪⁺ ([ fun⁺ lengthCB º⁺ ]⁺ ▪⁺ [ leq-ℕ ]⁺ ▪⁺ [ fun⁺ lengthCB ]⁺))) ⟩
    fun⁺ lengthCB º⁺ •⁺ leq-ℕ •⁺ fun⁺ lengthCB •⁺ fun⁺ lengthCB º⁺ •⁺ leq-ℕ •⁺ fun⁺ lengthCB
      ⊆⁺⟨ ⊆⁺-chain (fun⁺ lengthCB º⁺ ▪⁺ leq-ℕ ◇⁺) (fun⁺ lengthCB ▪⁺ fun⁺ lengthCB º⁺ ◇⁺) (idR⁺ ◇⁺) (fun⁺-simple lengthCB) ⟩
    fun⁺ lengthCB º⁺ •⁺ leq-ℕ •⁺ idR⁺ •⁺ leq-ℕ •⁺ fun⁺ lengthCB
      ⊆⁺⟨ ⊆⁺-chain (fun⁺ lengthCB º⁺ ◇⁺) (leq-ℕ ▪⁺ idR⁺ ◇⁺) (leq-ℕ ◇⁺) (proj₁ (idR⁺-r leq-ℕ)) ⟩
    fun⁺ lengthCB º⁺ •⁺ leq-ℕ •⁺ leq-ℕ •⁺ fun⁺ lengthCB
      ⊆⁺⟨ ⊆⁺-chain (fun⁺ lengthCB º⁺ ◇⁺) (leq-ℕ ▪⁺ leq-ℕ ◇⁺) (leq-ℕ ◇⁺) leq-ℕ-transitive ⟩
    fun⁺ lengthCB º⁺ •⁺ leq-ℕ •⁺ fun⁺ lengthCB
  □
  where open PreorderReasoning (⊆⁺-Preorder CoinBag CoinBag) renaming (_∼⟨_⟩_ to _⊆⁺⟨_⟩_; _∎ to _□)

S : Ḟ ⌊ CoinBagOD ⌋ (const ℕ) ↝⁺ (const ℕ)
S = fun⁺ total-value-alg

{-

monotonicity : α •⁺ Ṙ ⌊ CoinBagOD ⌋ R •⁺ α º⁺ ⊆⁺ R
monotonicity = 
  begin
    α •⁺ Ṙ ⌊ CoinBagOD ⌋ (fun⁺ lengthCB º⁺ •⁺ leq-ℕ •⁺ fun⁺ lengthCB) •⁺ α º⁺
      ⊆⁺⟨ {!!} ⟩
    fun⁺ lengthCB º⁺ •⁺ leq-ℕ •⁺ fun⁺ lengthCB
  □
  where open PreorderReasoning (⊆⁺-Preorder CoinBag CoinBag) renaming (_∼⟨_⟩_ to _⊆⁺⟨_⟩_; _∎ to _□)

-}
