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

count-alg : Ḟ ⌊ CoinBagOD ⌋ (const ℕ) ⇉ (const ℕ)
count-alg (false , _            ) = 0
count-alg (true  , c , n , _ , m) = n + m

count : ∀ {c} → CoinBag c → ℕ
count = fold count-alg


--------
-- specification

leq-ℕ : const {B = Coin} ℕ ↝⁺ const ℕ
leq-ℕ = wrap (const (flip _≤ℕ_))

leq-ℕ-reflexive : idR⁺ ⊆⁺ leq-ℕ
leq-ℕ-reflexive = {!!}

leq-ℕ-transitive : leq-ℕ •⁺ leq-ℕ ⊆⁺ leq-ℕ
leq-ℕ-transitive = wrap (const (wrap λ { x y (z , z≤x , y≤z) → DecTotalOrder.trans ℕ-DecTotalOrder y≤z z≤x }))

R : CoinBag ↝⁺ CoinBag
R = fun⁺ count º⁺ •⁺ leq-ℕ •⁺ fun⁺ count

R-transitive : R •⁺ R ⊆⁺ R
R-transitive =
  begin
    (fun⁺ count º⁺ •⁺ leq-ℕ •⁺ fun⁺ count) •⁺ (fun⁺ count º⁺ •⁺ leq-ℕ •⁺ fun⁺ count)
      ⊆⁺⟨ proj₁ (chain-normalise⁺
                  (([ fun⁺ count º⁺ ]⁺ ▪⁺ [ leq-ℕ ]⁺ ▪⁺ [ fun⁺ count ]⁺) ▪⁺ ([ fun⁺ count º⁺ ]⁺ ▪⁺ [ leq-ℕ ]⁺ ▪⁺ [ fun⁺ count ]⁺))) ⟩
    fun⁺ count º⁺ •⁺ leq-ℕ •⁺ fun⁺ count •⁺ fun⁺ count º⁺ •⁺ leq-ℕ •⁺ fun⁺ count
      ⊆⁺⟨ ⊆⁺-chain (fun⁺ count º⁺ ▪⁺ leq-ℕ ◇⁺) (fun⁺ count ▪⁺ fun⁺ count º⁺ ◇⁺) (idR⁺ ◇⁺) (fun⁺-simple count) ⟩
    fun⁺ count º⁺ •⁺ leq-ℕ •⁺ idR⁺ •⁺ leq-ℕ •⁺ fun⁺ count
      ⊆⁺⟨ ⊆⁺-chain (fun⁺ count º⁺ ◇⁺) (leq-ℕ ▪⁺ idR⁺ ◇⁺) (leq-ℕ ◇⁺) (proj₁ (idR⁺-r leq-ℕ)) ⟩
    fun⁺ count º⁺ •⁺ leq-ℕ •⁺ leq-ℕ •⁺ fun⁺ count
      ⊆⁺⟨ ⊆⁺-chain (fun⁺ count º⁺ ◇⁺) (leq-ℕ ▪⁺ leq-ℕ ◇⁺) (leq-ℕ ◇⁺) leq-ℕ-transitive ⟩
    fun⁺ count º⁺ •⁺ leq-ℕ •⁺ fun⁺ count
  □
  where open PreorderReasoning (⊆⁺-Preorder CoinBag CoinBag) renaming (_∼⟨_⟩_ to _⊆⁺⟨_⟩_; _∎ to _□)

S : Ḟ ⌊ CoinBagOD ⌋ (const ℕ) ↝⁺ (const ℕ)
S = fun⁺ total-value-alg

count-alg-monotonic : fun⁺ count-alg •⁺ Ṙ ⌊ CoinBagOD ⌋ leq-ℕ ⊆⁺ leq-ℕ •⁺ fun⁺ count-alg
count-alg-monotonic = {!!}

R-monotonic-lemma :
  (R' : const {B = Coin} ℕ ↝⁺ const ℕ) → (fun⁺ count-alg •⁺ Ṙ ⌊ CoinBagOD ⌋ R' ⊆⁺ R' •⁺ fun⁺ count-alg) →
  fun⁺ count-alg •⁺ Ṙ ⌊ CoinBagOD ⌋ R' •⁺ Ṙ ⌊ CoinBagOD ⌋ (fun⁺ count) •⁺ α º⁺ ⊆⁺ R' •⁺ fun⁺ count
R-monotonic-lemma R' monotonicity = {!!}

R-monotonic : α •⁺ Ṙ ⌊ CoinBagOD ⌋ R •⁺ α º⁺ ⊆⁺ R
R-monotonic = 
  begin
    α •⁺ Ṙ ⌊ CoinBagOD ⌋ (fun⁺ count º⁺ •⁺ leq-ℕ •⁺ fun⁺ count) •⁺ α º⁺
      ⊆⁺⟨ {!!} ⟩
    α •⁺ Ṙ ⌊ CoinBagOD ⌋ (fun⁺ count º⁺) •⁺ Ṙ ⌊ CoinBagOD ⌋ leq-ℕ •⁺ Ṙ ⌊ CoinBagOD ⌋ (fun⁺ count) •⁺ α º⁺
      ⊆⁺⟨ {!!} ⟩
    α •⁺ Ṙ ⌊ CoinBagOD ⌋ (fun⁺ count º⁺) •⁺ Ṙ ⌊ CoinBagOD ⌋ (leq-ℕ •⁺ idR⁺) •⁺ Ṙ ⌊ CoinBagOD ⌋ (fun⁺ count) •⁺ α º⁺
      ⊆⁺⟨ {!!} ⟩
    α •⁺ Ṙ ⌊ CoinBagOD ⌋ (fun⁺ count º⁺) •⁺ Ṙ ⌊ CoinBagOD ⌋ (leq-ℕ •⁺ leq-ℕ) •⁺ Ṙ ⌊ CoinBagOD ⌋ (fun⁺ count) •⁺ α º⁺
      ⊆⁺⟨ {!!} ⟩
    α •⁺ Ṙ ⌊ CoinBagOD ⌋ (fun⁺ count º⁺) •⁺ Ṙ ⌊ CoinBagOD ⌋ leq-ℕ •⁺ Ṙ ⌊ CoinBagOD ⌋ leq-ℕ •⁺ Ṙ ⌊ CoinBagOD ⌋ (fun⁺ count) •⁺ α º⁺
      ⊆⁺⟨ {!!} ⟩
    α •⁺ Ṙ ⌊ CoinBagOD ⌋ (fun⁺ count º⁺) •⁺ Ṙ ⌊ CoinBagOD ⌋ leq-ℕ •⁺ idR⁺ •⁺ Ṙ ⌊ CoinBagOD ⌋ leq-ℕ •⁺ Ṙ ⌊ CoinBagOD ⌋ (fun⁺ count) •⁺ α º⁺
      ⊆⁺⟨ {!!} ⟩
    α •⁺ Ṙ ⌊ CoinBagOD ⌋ (fun⁺ count º⁺) •⁺ Ṙ ⌊ CoinBagOD ⌋ leq-ℕ •⁺ fun⁺ count-alg º⁺ •⁺
    fun⁺ count-alg •⁺ Ṙ ⌊ CoinBagOD ⌋ leq-ℕ •⁺ Ṙ ⌊ CoinBagOD ⌋ (fun⁺ count) •⁺ α º⁺
      ⊆⁺⟨ {!!} ⟩
    α •⁺ Ṙ ⌊ CoinBagOD ⌋ (fun⁺ count) º⁺ •⁺ Ṙ ⌊ CoinBagOD ⌋ leq-ℕ •⁺ fun⁺ count-alg º⁺ •⁺
    fun⁺ count-alg •⁺ Ṙ ⌊ CoinBagOD ⌋ leq-ℕ •⁺ Ṙ ⌊ CoinBagOD ⌋ (fun⁺ count) •⁺ α º⁺
      ⊆⁺⟨ {!!} ⟩
    α •⁺ Ṙ ⌊ CoinBagOD ⌋ (fun⁺ count) º⁺ •⁺ Ṙ ⌊ CoinBagOD ⌋ (leq-ℕ º⁺) º⁺ •⁺ fun⁺ count-alg º⁺ •⁺
    fun⁺ count-alg •⁺ Ṙ ⌊ CoinBagOD ⌋ leq-ℕ •⁺ Ṙ ⌊ CoinBagOD ⌋ (fun⁺ count) •⁺ α º⁺
      ⊆⁺⟨ {!!} ⟩
    (fun⁺ count-alg •⁺ Ṙ ⌊ CoinBagOD ⌋ (leq-ℕ º⁺) •⁺ Ṙ ⌊ CoinBagOD ⌋ (fun⁺ count) •⁺ α º⁺) º⁺ •⁺
     fun⁺ count-alg •⁺ Ṙ ⌊ CoinBagOD ⌋ leq-ℕ      •⁺ Ṙ ⌊ CoinBagOD ⌋ (fun⁺ count) •⁺ α º⁺
      ⊆⁺⟨ •⁺-monotonic (º⁺-monotonic (R-monotonic-lemma (leq-ℕ º⁺) {!!})) (R-monotonic-lemma leq-ℕ count-alg-monotonic) ⟩
    (leq-ℕ º⁺ •⁺ fun⁺ count) º⁺ •⁺ leq-ℕ •⁺ fun⁺ count
      ⊆⁺⟨ ⊆⁺-chain-r ((leq-ℕ º⁺ •⁺ fun⁺ count) º⁺ ◇⁺) (fun⁺ count º⁺ ▪⁺ leq-ℕ ◇⁺) (proj₁ (º⁺-preserves-comp (leq-ℕ º⁺) (fun⁺ count))) ⟩
    fun⁺ count º⁺ •⁺ leq-ℕ •⁺ leq-ℕ •⁺ fun⁺ count
      ⊆⁺⟨ ⊆⁺-chain (fun⁺ count º⁺ ◇⁺) (leq-ℕ ▪⁺ leq-ℕ ◇⁺) (leq-ℕ ◇⁺) leq-ℕ-transitive ⟩
    fun⁺ count º⁺ •⁺ leq-ℕ •⁺ fun⁺ count
  □
  where open PreorderReasoning (⊆⁺-Preorder CoinBag CoinBag) renaming (_∼⟨_⟩_ to _⊆⁺⟨_⟩_; _∎ to _□)
