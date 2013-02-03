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
open import Thesis.Relation.Join
open import Thesis.Relation.Meet
import Thesis.Relation.GreedyTheorem as GreedyTheorem
open import Thesis.Examples.Nat hiding (_+_)
open import Thesis.Examples.List
open import Thesis.Examples.List.Sorted

open import Function using (id; const; _∘_; flip; _on_)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Bool using (Bool; false; true)
open import Data.Nat using (ℕ; _+_; _*_) renaming (_≤_ to _≤ℕ_; decTotalOrder to ℕ-DecTotalOrder)
open import Data.Nat.Properties using (_+-mono_) renaming (<-trans to <ℕ-trans)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_; curry) renaming (map to _**_)
open import Relation.Binary using (module DecTotalOrder)
import Relation.Binary.PreorderReasoning as PreorderReasoning
open import Relation.Binary.PropositionalEquality using (_≡_; refl)


--------
-- coins

data Coin : Set where
  1p : Coin
  2p : Coin
  5p : Coin

value : Coin → ℕ
value 1p = 1
value 2p = 2
value 5p = 5

_≤_ : Coin → Coin → Set
_≤_ = _≤ℕ_ on value


--------
-- coin bags as sorted coin lists

CoinBagOD : OrnDesc Coin ! ⌊ ListOD Coin ⌋
CoinBagOD = SListOD Coin (flip _≤_) (flip (DecTotalOrder.trans ℕ-DecTotalOrder))

CoinBag : Coin → Set
CoinBag = μ ⌊ CoinBagOD ⌋

total-value-alg : Ḟ ⌊ CoinBagOD ⌋ (const ℕ) ⇉ (const ℕ)
total-value-alg (false , _        ) = 0
total-value-alg (true  , c , _ , m) = value c + m

total-value : ∀ {c} → CoinBag c → ℕ
total-value = fold total-value-alg

count-alg : Ḟ ⌊ CoinBagOD ⌋ (const ℕ) ⇉ (const ℕ)
count-alg (false , _        ) = 0
count-alg (true  , c , _ , m) = 1 + m

count : ∀ {c} → CoinBag c → ℕ
count = fold count-alg


--------
-- specification

leq-ℕ : const {B = Coin} ℕ ↝⁺ const ℕ
leq-ℕ = wrap (const (flip _≤ℕ_))

leq-ℕ-reflexive : idR⁺ ⊆⁺ leq-ℕ
leq-ℕ-reflexive = wrap λ c → wrap λ { x .x refl → DecTotalOrder.refl ℕ-DecTotalOrder }

leq-ℕ-transitive : leq-ℕ •⁺ leq-ℕ ⊆⁺ leq-ℕ
leq-ℕ-transitive = wrap (const (wrap λ { x y (z , z≤x , y≤z) → DecTotalOrder.trans ℕ-DecTotalOrder y≤z z≤x }))

R : CoinBag ↝⁺ CoinBag
R = fun⁺ count º⁺ •⁺ leq-ℕ •⁺ fun⁺ count

postulate R-transitive : R •⁺ R ⊆⁺ R
{- [ Proved. ]
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
-}

S : Ḟ ⌊ CoinBagOD ⌋ (const ℕ) ↝⁺ (const ℕ)
S = fun⁺ total-value-alg

count-alg-monotonic : fun⁺ count-alg •⁺ Ṙ ⌊ CoinBagOD ⌋ leq-ℕ ⊆⁺ leq-ℕ •⁺ fun⁺ count-alg
count-alg-monotonic =
  wrap λ c → wrap λ { (false , _              ) ._ (._ , (_ , _ , refl) , refl) →
                        0 , refl , DecTotalOrder.refl ℕ-DecTotalOrder
                    ; (true  , d , d≤c , n) ._ (._ , (._ , (._ , (m , m≤n , refl) , refl) , refl) , refl) →
                        1 + n , refl , DecTotalOrder.refl ℕ-DecTotalOrder {1} +-mono m≤n }

postulate
  R-monotonic-lemma :
    (R' : const {B = Coin} ℕ ↝⁺ const ℕ) → (fun⁺ count-alg •⁺ Ṙ ⌊ CoinBagOD ⌋ R' ⊆⁺ R' •⁺ fun⁺ count-alg) →
    fun⁺ count-alg •⁺ Ṙ ⌊ CoinBagOD ⌋ R' •⁺ Ṙ ⌊ CoinBagOD ⌋ (fun⁺ count) •⁺ α º⁺ ⊆⁺ R' •⁺ fun⁺ count
{- [ Proved. ]
R-monotonic-lemma R' monotonicity =
  begin
    fun⁺ count-alg •⁺ Ṙ ⌊ CoinBagOD ⌋ R' •⁺ Ṙ ⌊ CoinBagOD ⌋ (fun⁺ count) •⁺ α º⁺
      ⊆⁺⟨ ⊆⁺-chain-r (fun⁺ count-alg ▪⁺ Ṙ ⌊ CoinBagOD ⌋ R' ◇⁺) (R' ▪⁺ fun⁺ count-alg ◇⁺) monotonicity ⟩
    R' •⁺ fun⁺ count-alg •⁺ Ṙ ⌊ CoinBagOD ⌋ (fun⁺ count) •⁺ α º⁺
      ⊆⁺⟨ ⊆⁺-chain (R' ▪⁺ fun⁺ count-alg ◇⁺) (Ṙ ⌊ CoinBagOD ⌋ (fun⁺ count) ◇⁺) (Ṙ ⌊ CoinBagOD ⌋ (foldR (fun⁺ count-alg)) ◇⁺)
            (Ṙ-monotonic ⌊ CoinBagOD ⌋ (proj₁ (fun⁺-preserves-fold ⌊ CoinBagOD ⌋ count-alg))) ⟩
    R' •⁺ fun⁺ count-alg •⁺ Ṙ ⌊ CoinBagOD ⌋ (foldR (fun⁺ count-alg)) •⁺ α º⁺
      ⊆⁺⟨ •⁺-monotonic-l R' (proj₂ (foldR-computation' ⌊ CoinBagOD ⌋ (fun⁺ count-alg))) ⟩
    R' •⁺ foldR (fun⁺ count-alg)
      ⊆⁺⟨ •⁺-monotonic-l R' (proj₂ (fun⁺-preserves-fold ⌊ CoinBagOD ⌋ count-alg)) ⟩
    R' •⁺ fun⁺ count
  □
  where open PreorderReasoning (⊆⁺-Preorder (μ ⌊ CoinBagOD ⌋) (const ℕ)) renaming (_∼⟨_⟩_ to _⊆⁺⟨_⟩_; _∎ to _□)
-}

postulate R-monotonic : α •⁺ Ṙ ⌊ CoinBagOD ⌋ R •⁺ α º⁺ ⊆⁺ R
{- [ Proved. ]
R-monotonic = 
  begin
    α •⁺ Ṙ ⌊ CoinBagOD ⌋ (fun⁺ count º⁺ •⁺ leq-ℕ •⁺ fun⁺ count) •⁺ α º⁺
      ⊆⁺⟨ ⊆⁺-chain (α ◇⁺) (Ṙ ⌊ CoinBagOD ⌋ (fun⁺ count º⁺ •⁺ leq-ℕ •⁺ fun⁺ count) ◇⁺)
            (Ṙ ⌊ CoinBagOD ⌋ (fun⁺ count º⁺) ▪⁺ Ṙ ⌊ CoinBagOD ⌋ leq-ℕ ▪⁺ Ṙ ⌊ CoinBagOD ⌋ (fun⁺ count) ◇⁺)
            (proj₁ (Ṙ-chain ⌊ CoinBagOD ⌋ (fun⁺ count º⁺ ▪⁺ leq-ℕ ▪⁺ fun⁺ count ◇⁺))) ⟩
    α •⁺ Ṙ ⌊ CoinBagOD ⌋ (fun⁺ count º⁺) •⁺ Ṙ ⌊ CoinBagOD ⌋ leq-ℕ •⁺ Ṙ ⌊ CoinBagOD ⌋ (fun⁺ count) •⁺ α º⁺
      ⊆⁺⟨ ⊆⁺-chain (α ▪⁺ Ṙ ⌊ CoinBagOD ⌋ (fun⁺ count º⁺) ◇⁺)
            (Ṙ ⌊ CoinBagOD ⌋ leq-ℕ ◇⁺) (Ṙ ⌊ CoinBagOD ⌋ (leq-ℕ •⁺ idR⁺) ◇⁺)
            (Ṙ-monotonic ⌊ CoinBagOD ⌋ (proj₂ (idR⁺-r leq-ℕ))) ⟩
    α •⁺ Ṙ ⌊ CoinBagOD ⌋ (fun⁺ count º⁺) •⁺ Ṙ ⌊ CoinBagOD ⌋ (leq-ℕ •⁺ idR⁺) •⁺ Ṙ ⌊ CoinBagOD ⌋ (fun⁺ count) •⁺ α º⁺
      ⊆⁺⟨ ⊆⁺-chain (α ▪⁺ Ṙ ⌊ CoinBagOD ⌋ (fun⁺ count º⁺) ◇⁺)
            (Ṙ ⌊ CoinBagOD ⌋ (leq-ℕ •⁺ idR⁺) ◇⁺) (Ṙ ⌊ CoinBagOD ⌋ (leq-ℕ •⁺ leq-ℕ) ◇⁺)
            (Ṙ-monotonic ⌊ CoinBagOD ⌋ (•⁺-monotonic-l leq-ℕ leq-ℕ-reflexive)) ⟩
    α •⁺ Ṙ ⌊ CoinBagOD ⌋ (fun⁺ count º⁺) •⁺ Ṙ ⌊ CoinBagOD ⌋ (leq-ℕ •⁺ leq-ℕ) •⁺ Ṙ ⌊ CoinBagOD ⌋ (fun⁺ count) •⁺ α º⁺
      ⊆⁺⟨ ⊆⁺-chain (α ▪⁺ Ṙ ⌊ CoinBagOD ⌋ (fun⁺ count º⁺) ◇⁺)
            (Ṙ ⌊ CoinBagOD ⌋ (leq-ℕ •⁺ leq-ℕ) ◇⁺) (Ṙ ⌊ CoinBagOD ⌋ leq-ℕ ▪⁺ Ṙ ⌊ CoinBagOD ⌋ leq-ℕ ◇⁺)
            (proj₁ (Ṙ-preserves-comp ⌊ CoinBagOD ⌋ leq-ℕ leq-ℕ)) ⟩
    α •⁺ Ṙ ⌊ CoinBagOD ⌋ (fun⁺ count º⁺) •⁺ Ṙ ⌊ CoinBagOD ⌋ leq-ℕ •⁺ Ṙ ⌊ CoinBagOD ⌋ leq-ℕ •⁺ Ṙ ⌊ CoinBagOD ⌋ (fun⁺ count) •⁺ α º⁺
      ⊆⁺⟨ ⊆⁺-chain-l (α ▪⁺ Ṙ ⌊ CoinBagOD ⌋ (fun⁺ count º⁺) ▪⁺ Ṙ ⌊ CoinBagOD ⌋ leq-ℕ ◇⁺)
            (proj₂ (idR⁺-l (Ṙ ⌊ CoinBagOD ⌋ leq-ℕ •⁺ Ṙ ⌊ CoinBagOD ⌋ (fun⁺ count) •⁺ α º⁺))) ⟩
    α •⁺ Ṙ ⌊ CoinBagOD ⌋ (fun⁺ count º⁺) •⁺ Ṙ ⌊ CoinBagOD ⌋ leq-ℕ •⁺ idR⁺ •⁺ Ṙ ⌊ CoinBagOD ⌋ leq-ℕ •⁺ Ṙ ⌊ CoinBagOD ⌋ (fun⁺ count) •⁺ α º⁺
      ⊆⁺⟨ ⊆⁺-chain (α ▪⁺ Ṙ ⌊ CoinBagOD ⌋ (fun⁺ count º⁺) ▪⁺ Ṙ ⌊ CoinBagOD ⌋ leq-ℕ ◇⁺)
            (idR⁺ ◇⁺) (fun⁺ count-alg º⁺ ▪⁺ fun⁺ count-alg ◇⁺)
            (fun⁺-entire count-alg) ⟩
    α •⁺ Ṙ ⌊ CoinBagOD ⌋ (fun⁺ count º⁺) •⁺ Ṙ ⌊ CoinBagOD ⌋ leq-ℕ •⁺ fun⁺ count-alg º⁺ •⁺
    fun⁺ count-alg •⁺ Ṙ ⌊ CoinBagOD ⌋ leq-ℕ •⁺ Ṙ ⌊ CoinBagOD ⌋ (fun⁺ count) •⁺ α º⁺
      ⊆⁺⟨ ⊆⁺-chain (α ◇⁺) (Ṙ ⌊ CoinBagOD ⌋ (fun⁺ count º⁺) ◇⁺)
            (Ṙ ⌊ CoinBagOD ⌋ (fun⁺ count) º⁺ ◇⁺)
            (proj₁ (Ṙ-preserves-conv ⌊ CoinBagOD ⌋ (fun⁺ count))) ⟩
    α •⁺ Ṙ ⌊ CoinBagOD ⌋ (fun⁺ count) º⁺ •⁺ Ṙ ⌊ CoinBagOD ⌋ leq-ℕ •⁺ fun⁺ count-alg º⁺ •⁺
    fun⁺ count-alg •⁺ Ṙ ⌊ CoinBagOD ⌋ leq-ℕ •⁺ Ṙ ⌊ CoinBagOD ⌋ (fun⁺ count) •⁺ α º⁺
      ⊆⁺⟨ ⊆⁺-chain (α ▪⁺ Ṙ ⌊ CoinBagOD ⌋ (fun⁺ count) º⁺ ◇⁺)
            (Ṙ ⌊ CoinBagOD ⌋ leq-ℕ ◇⁺) (Ṙ ⌊ CoinBagOD ⌋ (leq-ℕ º⁺) º⁺ ◇⁺)
            (proj₁ (Ṙ-preserves-conv ⌊ CoinBagOD ⌋ (leq-ℕ º⁺))) ⟩
    α •⁺ Ṙ ⌊ CoinBagOD ⌋ (fun⁺ count) º⁺ •⁺ Ṙ ⌊ CoinBagOD ⌋ (leq-ℕ º⁺) º⁺ •⁺ fun⁺ count-alg º⁺ •⁺
    fun⁺ count-alg •⁺ Ṙ ⌊ CoinBagOD ⌋ leq-ℕ •⁺ Ṙ ⌊ CoinBagOD ⌋ (fun⁺ count) •⁺ α º⁺
      ⊆⁺⟨ ⊆⁺-chain-r
            (α ▪⁺ Ṙ ⌊ CoinBagOD ⌋ (fun⁺ count) º⁺ ▪⁺ Ṙ ⌊ CoinBagOD ⌋ (leq-ℕ º⁺) º⁺ ▪⁺ fun⁺ count-alg º⁺ ◇⁺)
            ((fun⁺ count-alg •⁺ Ṙ ⌊ CoinBagOD ⌋ (leq-ℕ º⁺) •⁺ Ṙ ⌊ CoinBagOD ⌋ (fun⁺ count) •⁺ α º⁺) º⁺ ◇⁺)
            (proj₂ (º⁺-chain (fun⁺ count-alg ▪⁺ Ṙ ⌊ CoinBagOD ⌋ (leq-ℕ º⁺) ▪⁺ Ṙ ⌊ CoinBagOD ⌋ (fun⁺ count) ▪⁺ α º⁺ ◇⁺))) ⟩
    (fun⁺ count-alg •⁺ Ṙ ⌊ CoinBagOD ⌋ (leq-ℕ º⁺) •⁺ Ṙ ⌊ CoinBagOD ⌋ (fun⁺ count) •⁺ α º⁺) º⁺ •⁺
     fun⁺ count-alg •⁺ Ṙ ⌊ CoinBagOD ⌋  leq-ℕ     •⁺ Ṙ ⌊ CoinBagOD ⌋ (fun⁺ count) •⁺ α º⁺
      ⊆⁺⟨ •⁺-monotonic (º⁺-monotonic (R-monotonic-lemma (leq-ℕ º⁺) (fun⁺-monotonic-alg-lemma ⌊ CoinBagOD ⌋ count-alg leq-ℕ count-alg-monotonic)))
                      (R-monotonic-lemma leq-ℕ count-alg-monotonic) ⟩
    (leq-ℕ º⁺ •⁺ fun⁺ count) º⁺ •⁺ leq-ℕ •⁺ fun⁺ count
      ⊆⁺⟨ ⊆⁺-chain-r ((leq-ℕ º⁺ •⁺ fun⁺ count) º⁺ ◇⁺) (fun⁺ count º⁺ ▪⁺ leq-ℕ ◇⁺) (proj₁ (º⁺-preserves-comp (leq-ℕ º⁺) (fun⁺ count))) ⟩
    fun⁺ count º⁺ •⁺ leq-ℕ •⁺ leq-ℕ •⁺ fun⁺ count
      ⊆⁺⟨ ⊆⁺-chain (fun⁺ count º⁺ ◇⁺) (leq-ℕ ▪⁺ leq-ℕ ◇⁺) (leq-ℕ ◇⁺) leq-ℕ-transitive ⟩
    fun⁺ count º⁺ •⁺ leq-ℕ •⁺ fun⁺ count
  □
  where open PreorderReasoning (⊆⁺-Preorder CoinBag CoinBag) renaming (_∼⟨_⟩_ to _⊆⁺⟨_⟩_; _∎ to _□)
-}

nil : {X : Coin → Set} → Ḟ ⌊ CoinBagOD ⌋ X ↝⁺ Ḟ ⌊ CoinBagOD ⌋ X
nil = wrap λ { c (false , _) → return (false , tt)
             ; c (true  , _) → none }

cons-leq : {X : Coin → Set} → Ḟ ⌊ CoinBagOD ⌋ X ↝⁺ Ḟ ⌊ CoinBagOD ⌋ X
cons-leq = wrap λ { c (false , _    ) → none
                  ; c (true  , d , _) → (_≤_ d) >>= λ e → any>>= λ r → return (true , e , r) }


Q : Ḟ ⌊ CoinBagOD ⌋ (const ℕ) ↝⁺ Ḟ ⌊ CoinBagOD ⌋ (const ℕ)
Q = nil ∪⁺ cons-leq

greedy-condition :
  α •⁺ Ṙ ⌊ CoinBagOD ⌋ (foldR (fun⁺ total-value-alg) º⁺) •⁺ (Q ∩⁺ (fun⁺ total-value-alg º⁺ •⁺ fun⁺ total-value-alg)) º⁺
    ⊆⁺ R º⁺ •⁺ α •⁺ Ṙ ⌊ CoinBagOD ⌋ (foldR (fun⁺ total-value-alg) º⁺)
greedy-condition = {!!}

{-

open GreedyTheorem (⌊ CoinBagOD ⌋) R S R-transitive R-monotonic Q greedy-condition

solve : (c : Coin) (n : ℕ) → GreedySolution c n
solve c n = {!!}

-}
