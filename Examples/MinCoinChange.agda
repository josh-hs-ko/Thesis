-- Solving the minimum coin change problem with the Greedy Theorem and algebraic ornamentation.

module Thesis.Examples.MinCoinChange where

open import Thesis.Prelude.Category.Isomorphism
open import Thesis.Prelude.Function
open import Thesis.Prelude.InverseImage
open import Thesis.Prelude.Function.Fam
open import Thesis.Prelude.Preorder
open import Thesis.Description hiding (_*_)
open import Thesis.Ornament hiding (_*_)
open import Thesis.Ornament.SequentialComposition
open import Thesis.Ornament.ParallelComposition
open import Thesis.Ornament.ParallelComposition.Swap
open import Thesis.Ornament.RefinementSemantics
open import Thesis.Ornament.Algebraic
open import Thesis.Refinement
open import Thesis.Relation
open import Thesis.Relation.CompChain
open import Thesis.Relation.Fold
open import Thesis.Relation.Join
open import Thesis.Relation.Meet
import Thesis.Relation.GreedyTheorem as GreedyTheorem
open import Thesis.Examples.List
open import Thesis.Examples.List.Sorted

open import Function using (id; const; _∘_; flip; _on_)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Bool using (Bool; false; true)
open import Data.Nat using (ℕ; zero; suc; _+_; z≤n; s≤s) renaming (_≤_ to _≤ℕ_; decTotalOrder to ℕ-DecTotalOrder)
open import Data.Nat.Properties using (_+-mono_; module SemiringSolver); open Data.Nat.Properties.SemiringSolver renaming (con to :con)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary using (module DecTotalOrder)
import Relation.Binary.PreorderReasoning as PreorderReasoning
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)


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

≤ℕ-refl : {x : ℕ} → x ≤ℕ x
≤ℕ-refl = DecTotalOrder.refl ℕ-DecTotalOrder

≤ℕ-trans : ∀ {x y z} → x ≤ℕ y → y ≤ℕ z → x ≤ℕ z
≤ℕ-trans = DecTotalOrder.trans ℕ-DecTotalOrder

CoinBagOD : OrnDesc Coin ! ⌊ ListOD Coin ⌋
CoinBagOD = SListOD Coin (flip _≤_) (flip ≤ℕ-trans)

CoinBagD : Desc Coin
CoinBagD = ⌊ CoinBagOD ⌋

CoinBagO : Orn ! ⌊ ListOD Coin ⌋ CoinBagD
CoinBagO = ⌈ CoinBagOD ⌉

CoinBag : Coin → Set
CoinBag = μ CoinBagD

nil : ∀ {c} → CoinBag c
nil = con (false , tt)

cons : (d : Coin) → ∀ {c} → d ≤ c → CoinBag d → CoinBag c
cons d d≤c b = con (true , d , d≤c , b)


total-value-alg : Ḟ CoinBagD (const ℕ) ⇉ (const ℕ)
total-value-alg (false , _        ) = 0
total-value-alg (true  , c , _ , m) = value c + m

total-value : ∀ {c} → CoinBag c → ℕ
total-value = fold total-value-alg

count-alg : Ḟ CoinBagD (const ℕ) ⇉ (const ℕ)
count-alg (false , _        ) = 0
count-alg (true  , _ , _ , m) = 1 + m

count : ∀ {c} → CoinBag c → ℕ
count = fold count-alg


--------
-- specification

leq-ℕ : const {B = Coin} ℕ ↝⁺ const ℕ
leq-ℕ = wrap (const (flip _≤ℕ_))

leq-ℕ-reflexive : idR⁺ ⊆⁺ leq-ℕ
leq-ℕ-reflexive = wrap λ c → wrap λ { x .x refl → ≤ℕ-refl }

leq-ℕ-transitive : leq-ℕ •⁺ leq-ℕ ⊆⁺ leq-ℕ
leq-ℕ-transitive = wrap (const (wrap λ { x y (z , z≤x , y≤z) → ≤ℕ-trans y≤z z≤x }))

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

S : Ḟ CoinBagD (const ℕ) ↝⁺ (const ℕ)
S = fun⁺ total-value-alg

count-alg-monotonic : fun⁺ count-alg •⁺ Ṙ CoinBagD leq-ℕ ⊆⁺ leq-ℕ •⁺ fun⁺ count-alg
count-alg-monotonic =
  wrap λ c → wrap λ { (false , _              ) ._ (._ , (_ , _ , refl) , refl) →
                        0 , refl , DecTotalOrder.refl ℕ-DecTotalOrder
                    ; (true  , d , d≤c , n) ._ (._ , (._ , (._ , (m , m≤n , refl) , refl) , refl) , refl) →
                        1 + n , refl , ≤ℕ-refl {1} +-mono m≤n }

postulate
  R-monotonic-lemma :
    (R' : const {B = Coin} ℕ ↝⁺ const ℕ) → (fun⁺ count-alg •⁺ Ṙ CoinBagD R' ⊆⁺ R' •⁺ fun⁺ count-alg) →
    fun⁺ count-alg •⁺ Ṙ CoinBagD R' •⁺ Ṙ CoinBagD (fun⁺ count) •⁺ α º⁺ ⊆⁺ R' •⁺ fun⁺ count
{- [ Proved. ]
R-monotonic-lemma R' monotonicity =
  begin
    fun⁺ count-alg •⁺ Ṙ CoinBagD R' •⁺ Ṙ CoinBagD (fun⁺ count) •⁺ α º⁺
      ⊆⁺⟨ ⊆⁺-chain-r (fun⁺ count-alg ▪⁺ Ṙ CoinBagD R' ◇⁺) (R' ▪⁺ fun⁺ count-alg ◇⁺) monotonicity ⟩
    R' •⁺ fun⁺ count-alg •⁺ Ṙ CoinBagD (fun⁺ count) •⁺ α º⁺
      ⊆⁺⟨ ⊆⁺-chain (R' ▪⁺ fun⁺ count-alg ◇⁺) (Ṙ CoinBagD (fun⁺ count) ◇⁺) (Ṙ CoinBagD (foldR (fun⁺ count-alg)) ◇⁺)
            (Ṙ-monotonic CoinBagD (proj₁ (fun⁺-preserves-fold CoinBagD count-alg))) ⟩
    R' •⁺ fun⁺ count-alg •⁺ Ṙ CoinBagD (foldR (fun⁺ count-alg)) •⁺ α º⁺
      ⊆⁺⟨ •⁺-monotonic-l R' (proj₂ (foldR-computation' CoinBagD (fun⁺ count-alg))) ⟩
    R' •⁺ foldR (fun⁺ count-alg)
      ⊆⁺⟨ •⁺-monotonic-l R' (proj₂ (fun⁺-preserves-fold CoinBagD count-alg)) ⟩
    R' •⁺ fun⁺ count
  □
  where open PreorderReasoning (⊆⁺-Preorder (μ CoinBagD) (const ℕ)) renaming (_∼⟨_⟩_ to _⊆⁺⟨_⟩_; _∎ to _□)
-}

postulate R-monotonic : α •⁺ Ṙ CoinBagD R •⁺ α º⁺ ⊆⁺ R
{- [ Proved. ]
R-monotonic = 
  begin
    α •⁺ Ṙ CoinBagD (fun⁺ count º⁺ •⁺ leq-ℕ •⁺ fun⁺ count) •⁺ α º⁺
      ⊆⁺⟨ ⊆⁺-chain (α ◇⁺) (Ṙ CoinBagD (fun⁺ count º⁺ •⁺ leq-ℕ •⁺ fun⁺ count) ◇⁺)
            (Ṙ CoinBagD (fun⁺ count º⁺) ▪⁺ Ṙ CoinBagD leq-ℕ ▪⁺ Ṙ CoinBagD (fun⁺ count) ◇⁺)
            (proj₁ (Ṙ-chain CoinBagD (fun⁺ count º⁺ ▪⁺ leq-ℕ ▪⁺ fun⁺ count ◇⁺))) ⟩
    α •⁺ Ṙ CoinBagD (fun⁺ count º⁺) •⁺ Ṙ CoinBagD leq-ℕ •⁺ Ṙ CoinBagD (fun⁺ count) •⁺ α º⁺
      ⊆⁺⟨ ⊆⁺-chain (α ▪⁺ Ṙ CoinBagD (fun⁺ count º⁺) ◇⁺)
            (Ṙ CoinBagD leq-ℕ ◇⁺) (Ṙ CoinBagD (leq-ℕ •⁺ idR⁺) ◇⁺)
            (Ṙ-monotonic CoinBagD (proj₂ (idR⁺-r leq-ℕ))) ⟩
    α •⁺ Ṙ CoinBagD (fun⁺ count º⁺) •⁺ Ṙ CoinBagD (leq-ℕ •⁺ idR⁺) •⁺ Ṙ CoinBagD (fun⁺ count) •⁺ α º⁺
      ⊆⁺⟨ ⊆⁺-chain (α ▪⁺ Ṙ CoinBagD (fun⁺ count º⁺) ◇⁺)
            (Ṙ CoinBagD (leq-ℕ •⁺ idR⁺) ◇⁺) (Ṙ CoinBagD (leq-ℕ •⁺ leq-ℕ) ◇⁺)
            (Ṙ-monotonic CoinBagD (•⁺-monotonic-l leq-ℕ leq-ℕ-reflexive)) ⟩
    α •⁺ Ṙ CoinBagD (fun⁺ count º⁺) •⁺ Ṙ CoinBagD (leq-ℕ •⁺ leq-ℕ) •⁺ Ṙ CoinBagD (fun⁺ count) •⁺ α º⁺
      ⊆⁺⟨ ⊆⁺-chain (α ▪⁺ Ṙ CoinBagD (fun⁺ count º⁺) ◇⁺)
            (Ṙ CoinBagD (leq-ℕ •⁺ leq-ℕ) ◇⁺) (Ṙ CoinBagD leq-ℕ ▪⁺ Ṙ CoinBagD leq-ℕ ◇⁺)
            (proj₁ (Ṙ-preserves-comp CoinBagD leq-ℕ leq-ℕ)) ⟩
    α •⁺ Ṙ CoinBagD (fun⁺ count º⁺) •⁺ Ṙ CoinBagD leq-ℕ •⁺ Ṙ CoinBagD leq-ℕ •⁺ Ṙ CoinBagD (fun⁺ count) •⁺ α º⁺
      ⊆⁺⟨ ⊆⁺-chain-l (α ▪⁺ Ṙ CoinBagD (fun⁺ count º⁺) ▪⁺ Ṙ CoinBagD leq-ℕ ◇⁺)
            (proj₂ (idR⁺-l (Ṙ CoinBagD leq-ℕ •⁺ Ṙ CoinBagD (fun⁺ count) •⁺ α º⁺))) ⟩
    α •⁺ Ṙ CoinBagD (fun⁺ count º⁺) •⁺ Ṙ CoinBagD leq-ℕ •⁺ idR⁺ •⁺ Ṙ CoinBagD leq-ℕ •⁺ Ṙ CoinBagD (fun⁺ count) •⁺ α º⁺
      ⊆⁺⟨ ⊆⁺-chain (α ▪⁺ Ṙ CoinBagD (fun⁺ count º⁺) ▪⁺ Ṙ CoinBagD leq-ℕ ◇⁺)
            (idR⁺ ◇⁺) (fun⁺ count-alg º⁺ ▪⁺ fun⁺ count-alg ◇⁺)
            (fun⁺-entire count-alg) ⟩
    α •⁺ Ṙ CoinBagD (fun⁺ count º⁺) •⁺ Ṙ CoinBagD leq-ℕ •⁺ fun⁺ count-alg º⁺ •⁺
    fun⁺ count-alg •⁺ Ṙ CoinBagD leq-ℕ •⁺ Ṙ CoinBagD (fun⁺ count) •⁺ α º⁺
      ⊆⁺⟨ ⊆⁺-chain (α ◇⁺) (Ṙ CoinBagD (fun⁺ count º⁺) ◇⁺)
            (Ṙ CoinBagD (fun⁺ count) º⁺ ◇⁺)
            (proj₁ (Ṙ-preserves-conv CoinBagD (fun⁺ count))) ⟩
    α •⁺ Ṙ CoinBagD (fun⁺ count) º⁺ •⁺ Ṙ CoinBagD leq-ℕ •⁺ fun⁺ count-alg º⁺ •⁺
    fun⁺ count-alg •⁺ Ṙ CoinBagD leq-ℕ •⁺ Ṙ CoinBagD (fun⁺ count) •⁺ α º⁺
      ⊆⁺⟨ ⊆⁺-chain (α ▪⁺ Ṙ CoinBagD (fun⁺ count) º⁺ ◇⁺)
            (Ṙ CoinBagD leq-ℕ ◇⁺) (Ṙ CoinBagD (leq-ℕ º⁺) º⁺ ◇⁺)
            (proj₁ (Ṙ-preserves-conv CoinBagD (leq-ℕ º⁺))) ⟩
    α •⁺ Ṙ CoinBagD (fun⁺ count) º⁺ •⁺ Ṙ CoinBagD (leq-ℕ º⁺) º⁺ •⁺ fun⁺ count-alg º⁺ •⁺
    fun⁺ count-alg •⁺ Ṙ CoinBagD leq-ℕ •⁺ Ṙ CoinBagD (fun⁺ count) •⁺ α º⁺
      ⊆⁺⟨ ⊆⁺-chain-r
            (α ▪⁺ Ṙ CoinBagD (fun⁺ count) º⁺ ▪⁺ Ṙ CoinBagD (leq-ℕ º⁺) º⁺ ▪⁺ fun⁺ count-alg º⁺ ◇⁺)
            ((fun⁺ count-alg •⁺ Ṙ CoinBagD (leq-ℕ º⁺) •⁺ Ṙ CoinBagD (fun⁺ count) •⁺ α º⁺) º⁺ ◇⁺)
            (proj₂ (º⁺-chain (fun⁺ count-alg ▪⁺ Ṙ CoinBagD (leq-ℕ º⁺) ▪⁺ Ṙ CoinBagD (fun⁺ count) ▪⁺ α º⁺ ◇⁺))) ⟩
    (fun⁺ count-alg •⁺ Ṙ CoinBagD (leq-ℕ º⁺) •⁺ Ṙ CoinBagD (fun⁺ count) •⁺ α º⁺) º⁺ •⁺
     fun⁺ count-alg •⁺ Ṙ CoinBagD  leq-ℕ     •⁺ Ṙ CoinBagD (fun⁺ count) •⁺ α º⁺
      ⊆⁺⟨ •⁺-monotonic (º⁺-monotonic (R-monotonic-lemma (leq-ℕ º⁺) (fun⁺-monotonic-alg-lemma CoinBagD count-alg leq-ℕ count-alg-monotonic)))
                      (R-monotonic-lemma leq-ℕ count-alg-monotonic) ⟩
    (leq-ℕ º⁺ •⁺ fun⁺ count) º⁺ •⁺ leq-ℕ •⁺ fun⁺ count
      ⊆⁺⟨ ⊆⁺-chain-r ((leq-ℕ º⁺ •⁺ fun⁺ count) º⁺ ◇⁺) (fun⁺ count º⁺ ▪⁺ leq-ℕ ◇⁺) (proj₁ (º⁺-preserves-comp (leq-ℕ º⁺) (fun⁺ count))) ⟩
    fun⁺ count º⁺ •⁺ leq-ℕ •⁺ leq-ℕ •⁺ fun⁺ count
      ⊆⁺⟨ ⊆⁺-chain (fun⁺ count º⁺ ◇⁺) (leq-ℕ ▪⁺ leq-ℕ ◇⁺) (leq-ℕ ◇⁺) leq-ℕ-transitive ⟩
    fun⁺ count º⁺ •⁺ leq-ℕ •⁺ fun⁺ count
  □
  where open PreorderReasoning (⊆⁺-Preorder CoinBag CoinBag) renaming (_∼⟨_⟩_ to _⊆⁺⟨_⟩_; _∎ to _□)
-}

isNil : {X : Coin → Set} → Ḟ CoinBagD X ↝⁺ Ḟ CoinBagD X
isNil = wrap λ { c (false , _) → return (false , tt)
             ; c (true  , _) → none }

cons-leq : {X : Coin → Set} → Ḟ CoinBagD X ↝⁺ Ḟ CoinBagD X
cons-leq = wrap λ { c (false , _    ) → none
                  ; c (true  , d , _) → (_≤_ d) >>= λ e → any>>= λ r → return (true , e , r) }


Q : Ḟ CoinBagD (const ℕ) ↝⁺ Ḟ CoinBagD (const ℕ)
Q = isNil ∪⁺ cons-leq

CoinBag'OD : OrnDesc (Coin × ℕ) proj₁ CoinBagD
CoinBag'OD = algOrn CoinBagD (fun⁺ total-value-alg)

CoinBag'D : Desc (Coin × ℕ)
CoinBag'D = ⌊ CoinBag'OD ⌋

CoinBag'O : Orn proj₁ CoinBagD CoinBag'D
CoinBag'O = ⌈ CoinBag'OD ⌉

CoinBag' : Coin → ℕ → Set
CoinBag' c n = μ CoinBag'D (c , n)

nil' : {c : Coin} → CoinBag' c 0
nil' = con ((false , tt) , refl , tt)

cons' : (d : Coin) → ∀ {c} → d ≤ c → ∀ {m n} → value d + m ≡ n → CoinBag' d m → CoinBag' c n
cons' d d≤c {m} eq b = con ((true , d , d≤c , m) , eq , b)

data CoinCompareView : Coin → Coin → Set where
  1p≤1p : CoinCompareView 1p 1p
  1p≤2p : CoinCompareView 1p 2p
  1p≤5p : CoinCompareView 1p 5p
  2p≤2p : CoinCompareView 2p 2p
  2p≤5p : CoinCompareView 2p 5p
  5p≤5p : CoinCompareView 5p 5p

coinCompareView : (c d : Coin) → c ≤ d → CoinCompareView c d
coinCompareView 1p 1p c≤d = 1p≤1p
coinCompareView 1p 2p c≤d = 1p≤2p
coinCompareView 1p 5p c≤d = 1p≤5p
coinCompareView 2p 1p (s≤s ())
coinCompareView 2p 2p c≤d = 2p≤2p
coinCompareView 2p 5p c≤d = 2p≤5p
coinCompareView 5p 1p (s≤s ())
coinCompareView 5p 2p (s≤s (s≤s ()))
coinCompareView 5p 5p c≤d = 5p≤5p

data CoinBag'View : {c : Coin} {n : ℕ} → CoinBag' c n → Set where
  empty : {c : Coin} → CoinBag'View {c} {0} (con ((false , tt) , refl , tt))
  1p1p  : {m : ℕ} (l : 1p ≤ 1p) (b : CoinBag' 1p m) → CoinBag'View {1p} {1 + m} (cons' 1p l refl b)
  2p1p  : {m : ℕ} (l : 1p ≤ 2p) (b : CoinBag' 1p m) → CoinBag'View {2p} {1 + m} (cons' 1p l refl b)
  2p2p  : {m : ℕ} (l : 2p ≤ 2p) (b : CoinBag' 2p m) → CoinBag'View {2p} {2 + m} (cons' 2p l refl b)
  5p1p  : {m : ℕ} (l : 1p ≤ 5p) (b : CoinBag' 1p m) → CoinBag'View {5p} {1 + m} (cons' 1p l refl b)
  5p2p  : {m : ℕ} (l : 2p ≤ 5p) (b : CoinBag' 2p m) → CoinBag'View {5p} {2 + m} (cons' 2p l refl b)
  5p5p  : {m : ℕ} (l : 5p ≤ 5p) (b : CoinBag' 5p m) → CoinBag'View {5p} {5 + m} (cons' 5p l refl b)

-- Cannot reuse CoinCompareView here, mysteriously
viewCoinBag' : {c : Coin} {n : ℕ} (b : CoinBag' c n) → CoinBag'View b
viewCoinBag' {c}  {.0}       (con ((false , tt) , refl , tt))       = empty
viewCoinBag' {1p} {.(1 + m)} (con ((true , 1p , l , m) , refl , b)) = 1p1p l b
viewCoinBag' {1p} {n}        (con ((true , 2p , s≤s () , m) , eq , b))
viewCoinBag' {1p} {n}        (con ((true , 5p , s≤s () , m) , eq , b))
viewCoinBag' {2p} {.(1 + m)} (con ((true , 1p , l , m) , refl , b)) = 2p1p l b
viewCoinBag' {2p} {.(2 + m)} (con ((true , 2p , l , m) , refl , b)) = 2p2p l b
viewCoinBag' {2p} {n}        (con ((true , 5p , s≤s (s≤s ()) , m) , eq , b))
viewCoinBag' {5p} {.(1 + m)} (con ((true , 1p , l , m) , refl , b)) = 5p1p l b
viewCoinBag' {5p} {.(2 + m)} (con ((true , 2p , l , m) , refl , b)) = 5p2p l b
viewCoinBag' {5p} {.(5 + m)} (con ((true , 5p , l , m) , refl , b)) = 5p5p l b

leq-count-fusion-condition : leq-ℕ º⁺ •⁺ fun⁺ count-alg ≃⁺ (leq-ℕ º⁺ •⁺ fun⁺ count-alg) •⁺ Ṙ CoinBagD (leq-ℕ º⁺)
leq-count-fusion-condition =
  (begin
     leq-ℕ º⁺ •⁺ fun⁺ count-alg
       ⊆⁺⟨ proj₂ (idR⁺-r (leq-ℕ º⁺ •⁺ fun⁺ count-alg)) ⟩
     (leq-ℕ º⁺ •⁺ fun⁺ count-alg) •⁺ idR⁺
       ⊆⁺⟨ •⁺-monotonic-l (leq-ℕ º⁺ •⁺ fun⁺ count-alg) (proj₂ (Ṙ-preserves-idR⁺ CoinBagD)) ⟩
     (leq-ℕ º⁺ •⁺ fun⁺ count-alg) •⁺ Ṙ CoinBagD idR⁺
       ⊆⁺⟨ •⁺-monotonic-l (leq-ℕ º⁺ •⁺ fun⁺ count-alg) (Ṙ-monotonic CoinBagD (proj₂ º⁺-preserves-idR⁺)) ⟩
     (leq-ℕ º⁺ •⁺ fun⁺ count-alg) •⁺ Ṙ CoinBagD (idR⁺ º⁺)
       ⊆⁺⟨ •⁺-monotonic-l (leq-ℕ º⁺ •⁺ fun⁺ count-alg) (Ṙ-monotonic CoinBagD (º⁺-monotonic leq-ℕ-reflexive)) ⟩
     (leq-ℕ º⁺ •⁺ fun⁺ count-alg) •⁺ Ṙ CoinBagD (leq-ℕ º⁺)
   □) ,
  (begin
     (leq-ℕ º⁺ •⁺ fun⁺ count-alg) •⁺ Ṙ CoinBagD (leq-ℕ º⁺)
       ⊆⁺⟨ proj₁ (•⁺-assoc (leq-ℕ º⁺) (fun⁺ count-alg) (Ṙ CoinBagD (leq-ℕ º⁺))) ⟩
     leq-ℕ º⁺ •⁺ fun⁺ count-alg •⁺ Ṙ CoinBagD (leq-ℕ º⁺)
       ⊆⁺⟨ •⁺-monotonic-l (leq-ℕ º⁺) (fun⁺-monotonic-alg-lemma CoinBagD count-alg leq-ℕ count-alg-monotonic) ⟩
     leq-ℕ º⁺ •⁺ leq-ℕ º⁺ •⁺ fun⁺ count-alg
       ⊆⁺⟨ ⊆⁺-chain-r (leq-ℕ º⁺ ▪⁺ leq-ℕ º⁺ ◇⁺) ((leq-ℕ •⁺ leq-ℕ) º⁺ ◇⁺) (proj₂ (º⁺-preserves-comp leq-ℕ leq-ℕ)) ⟩
     (leq-ℕ •⁺ leq-ℕ) º⁺ •⁺ fun⁺ count-alg
       ⊆⁺⟨ •⁺-monotonic-r (fun⁺ count-alg) (º⁺-monotonic leq-ℕ-transitive) ⟩
     leq-ℕ º⁺ •⁺ fun⁺ count-alg
   □)
  where open PreorderReasoning (⊆⁺-Preorder (Ḟ CoinBagD (const ℕ)) (const ℕ)) renaming (_∼⟨_⟩_ to _⊆⁺⟨_⟩_; _∎ to _□)

leq-count-fusion : leq-ℕ º⁺ •⁺ foldR {D = CoinBagD} (fun⁺ count-alg) ≃⁺ foldR (leq-ℕ º⁺ •⁺ fun⁺ count-alg)
leq-count-fusion = foldR-fusion CoinBagD (leq-ℕ º⁺) (fun⁺ count-alg) (leq-ℕ º⁺ •⁺ fun⁺ count-alg) leq-count-fusion-condition

CoinBag''OD : OrnDesc (proj₁ ⋈ proj₁) pull CoinBagD
CoinBag''OD = CoinBag'O ⊗ ⌈ algOrn CoinBagD (leq-ℕ º⁺ •⁺ fun⁺ count-alg) ⌉

CoinBag''D : Desc (proj₁ ⋈ proj₁)
CoinBag''D = ⌊ CoinBag''OD ⌋

CoinBag''O : Orn pull CoinBagD CoinBag''D
CoinBag''O = ⌈ CoinBag''OD ⌉

CoinBag'' : Coin → ℕ → ℕ → Set
CoinBag'' c n l = μ CoinBag''D (ok (c , n) , ok (c , l))

nil'' : {c : Coin} {l : ℕ} → CoinBag'' c 0 l
nil'' = con ((false , tt) , refl , (false , tt) , (0 , refl , z≤n) , refl , tt)

cons'' : (d : Coin) → ∀ {c} → d ≤ c → ∀ {n l l'} → 1 + l ≤ℕ l' → CoinBag'' d n l → CoinBag'' c (value d + n) l'
cons'' d {c} d≤c {n} {l} {l'} 1+l≤l' b =
  con ((true , d , d≤c , n) , refl , (true , d , d≤c , l) , (1 + l , refl , 1+l≤l') , refl , refl , refl , b)

inject : {c : Coin} {n : ℕ} → (b : CoinBag' c n) → ∀ {m} → count (forget CoinBag'O b) ≤ℕ m → CoinBag'' c n m
inject {c} {n} b {m} l≤m =
  Iso.from Fun
    (Refinement.i (FRefinement.comp
                     (toFRefinement (⊗-FSwap CoinBag'O ⌈ algOrn CoinBagD (leq-ℕ º⁺ •⁺ fun⁺ count-alg) ⌉
                                       idFSwap (algOrn-FSwap CoinBagD (leq-ℕ º⁺ •⁺ fun⁺ count-alg))))
                     (ok (ok (c , n) , ok (c , m)))))
    (forget CoinBag'O b ,
     proj₂ (Iso.to Fun (Refinement.i (FRefinement.comp (RSem' CoinBag'O) (ok (c , n)))) b) ,
     modus-ponens-⊆⁺ (proj₁ leq-count-fusion) c (forget CoinBag'O b) m
       (count (forget CoinBag'O b) ,
        modus-ponens-⊆⁺ (proj₁ (fun⁺-preserves-fold CoinBagD count-alg)) c (forget CoinBag'O b) (count (forget CoinBag'O b)) refl ,
        l≤m))

relax : {c : Coin} {n : ℕ} {l : ℕ} → (b : CoinBag'' c n l) → ∀ {d} → c ≤ d → CoinBag'' d n l
relax (con ((false , _) , refl , (false , _) , (._ , refl , lep) , _)) c≤d = nil''
relax (con ((false , _) , _ , (true , _) , _ , () , _)) c≤d
relax (con ((true  , _) , _ , (false , _) , _ , () , _)) c≤d
relax (con ((true , e , e≤c , n) , refl ,
            (true , .e , .e≤c , l) , (._ , refl , lep) , refl , refl , refl , b)) c≤d = cons'' e (≤ℕ-trans e≤c c≤d) lep b

insert1 : {c : Coin} {n : ℕ} {l l' : ℕ} → 1 + l ≤ℕ l' → CoinBag'' c n l → CoinBag'' c (1 + n) l'
insert1 {1p} {l = l} {l'} 1+l≤l' (con ((false , _) , refl , (false , _) , (._ , refl , lep) , _)) = cons'' 1p (s≤s z≤n) 1+l≤l' nil''
insert1 {2p} {l = l} {l'} 1+l≤l' (con ((false , _) , refl , (false , _) , (._ , refl , lep) , _)) = cons'' 1p (s≤s z≤n) 1+l≤l' nil''
insert1 {5p} {l = l} {l'} 1+l≤l' (con ((false , _) , refl , (false , _) , (._ , refl , lep) , _)) = cons'' 1p (s≤s z≤n) 1+l≤l' nil''
insert1                   1+l≤l' (con ((false , _) , _    , (true  , _) , _ , () , _))
insert1                   1+l≤l' (con ((true  , _) , _    , (false , _) , _ , () , _))
insert1 {c}  {l = l} {l'} 1+l≤l' (con ((true  , e , e≤c , n) , refl , (true , .e , .e≤c , _) , (._ , refl , lep) , refl , refl , refl , b)) =
  subst (λ m → CoinBag'' c m l')
        (solve 2 (λ n' ve → ve :+ (:con 1 :+ n') := :con 1 :+ (ve :+ n')) refl n (value e))
        (cons'' e {c} e≤c 1+l≤l' (insert1 lep b))

greedy-lemma : (c d : Coin) → d ≤ c → (m n : ℕ) → value d + m ≡ value c + n → (b : CoinBag' d m) → CoinBag'' c n (count (forget CoinBag'O b))
greedy-lemma  c   d  d≤c  m       n _    b with coinCompareView d c d≤c
greedy-lemma .1p .1p _   .n       n refl b | 1p≤1p = inject b ≤ℕ-refl
greedy-lemma .2p .1p _   .(1 + n) n refl b | 1p≤2p with viewCoinBag' b
greedy-lemma .2p .1p d≤c .(1 + n) n refl .(cons' 1p l refl b) | 1p≤2p
  | 1p1p l b = relax (inject b (z≤n {1} +-mono ≤ℕ-refl {count (forget CoinBag'O b)})) (s≤s z≤n)
greedy-lemma .5p .1p _   .(4 + n) n refl b | 1p≤5p with viewCoinBag' b
greedy-lemma .5p .1p d≤c .(4 + n) n refl .(cons' 1p l₀ refl b) | 1p≤5p
  | 1p1p l₀ b with viewCoinBag' b
greedy-lemma .5p .1p d≤c .(4 + n) n refl .(cons' 1p l₀ refl (cons' 1p l₁ refl b)) | 1p≤5p
  | 1p1p l₀ .(cons' 1p l₁ refl b)
  | 1p1p l₁ b with viewCoinBag' b
greedy-lemma .5p .1p d≤c .(4 + n) n refl .(cons' 1p l₀ refl (cons' 1p l₁ refl (cons' 1p l₂ refl b)))
  | 1p≤5p
  | 1p1p l₀ .(cons' 1p l₁ refl (cons' 1p l₂ refl b))
  | 1p1p l₁ .(cons' 1p l₂ refl b)
  | 1p1p l₂ b with viewCoinBag' b
greedy-lemma .5p .1p d≤c .(4 + n) n refl .(cons' 1p l₀ refl (cons' 1p l₁ refl (cons' 1p l₂ refl (cons' 1p l₃ refl b))))
  | 1p≤5p
  | 1p1p l₀ .(cons' 1p l₁ refl (cons' 1p l₂ refl (cons' 1p l₃ refl b)))
  | 1p1p l₁ .(cons' 1p l₂ refl (cons' 1p l₃ refl b))
  | 1p1p l₂ .(cons' 1p l₃ refl b)
  | 1p1p l₃ b = relax (inject b (z≤n {4} +-mono ≤ℕ-refl {count (forget CoinBag'O b)})) (s≤s z≤n)
greedy-lemma .2p .2p _   .n       n refl b | 2p≤2p = inject b ≤ℕ-refl
greedy-lemma .5p .2p _   .(3 + n) n refl b
  | 2p≤5p with viewCoinBag' b
greedy-lemma .5p .2p d≤c .(3 + n) n refl .(cons' 1p l₀ refl b)
  | 2p≤5p
  | 2p1p l₀ b with viewCoinBag' b
greedy-lemma .5p .2p d≤c .(3 + n) n refl .(cons' 1p l₀ refl (cons' 1p l₁ refl b))
  | 2p≤5p
  | 2p1p l₀ .(cons' 1p l₁ refl b)
  | 1p1p l₁ b with viewCoinBag' b
greedy-lemma .5p .2p d≤c .(3 + n) n refl .(cons' 1p l₀ refl (cons' 1p l₁ refl b))
  | 2p≤5p
  | 2p1p l₀ .(cons' 1p l₁ refl (cons' 1p l₂ refl b))
  | 1p1p l₁ .(cons' 1p l₂ refl b)
  | 1p1p l₂ b = relax (inject b (z≤n {3} +-mono ≤ℕ-refl {count (forget CoinBag'O b)})) (s≤s z≤n)
greedy-lemma .5p .2p d≤c .(3 + n) n refl .(cons' 2p l₀ refl b)
  | 2p≤5p
  | 2p2p l₀ b
  with viewCoinBag' b
greedy-lemma .5p .2p d≤c .(3 + n) n refl .(cons' 2p l₀ refl (cons' 1p l₁ refl b))
  | 2p≤5p
  | 2p2p l₀ .(cons' 1p l₁ refl b)
  | 2p1p l₁ b = relax (inject b (z≤n {2} +-mono ≤ℕ-refl {count (forget CoinBag'O b)})) (s≤s z≤n)
greedy-lemma .5p .2p d≤c .(4 + m) .(1 + m) refl .(cons' 2p l₀ refl con (cons' 2p l₁ refl b))
  | 2p≤5p
  | 2p2p l₀ .(cons' 2p l₁ refl b)
  | 2p2p {m} l₁ b = insert1 (z≤n {1} +-mono ≤ℕ-refl {1 + count (forget CoinBag'O b)}) (relax (inject b ≤ℕ-refl) (s≤s (s≤s z≤n)))
greedy-lemma .5p .5p _   .n       n refl b | 5p≤5p = inject b ≤ℕ-refl

greedy-condition :
  α •⁺ Ṙ CoinBagD (foldR (fun⁺ total-value-alg) º⁺) •⁺ (Q ∩⁺ (fun⁺ total-value-alg º⁺ •⁺ fun⁺ total-value-alg)) º⁺
    ⊆⁺ R º⁺ •⁺ α •⁺ Ṙ CoinBagD (foldR (fun⁺ total-value-alg) º⁺)
greedy-condition = wrap λ c →
  wrap λ { (false , _) ._ (._ , ((false , _) , (inj₁ refl , .0 , refl , refl) , _ , _ , refl) , refl) →
             nil , ((false , tt) , (tt , tt , refl) , refl) , (zero , (zero , refl , z≤n) , refl)
         ; (false , _) ._ (_ , ((true  , _) , (inj₁ () , _) , _) , refl)
         ; (false , _) ._ (_ , ((false , _) , (inj₂ () , _) , _) , refl)
         ; (false , _) ._ (_ , ((true  , _) , (inj₂ (_ , _ , _ , ()) , _) , _) , refl)
         ; (true  , x) ._ (_ , ((false , _) , (inj₁ () , _) , _) , refl)
         ; (true  , x) ._ (_ , ((true  , _) , (inj₁ () , _) , _) , refl)
         ; (true  , x) ._ (_ , ((false , _) , (inj₂ () , _) , _) , refl)
         ; (true  , d , d≤c , n) ._
           (._ , ((true  , d' , d'≤c , n') , (inj₂ (._ , d'≤d , ._ , refl) , ._ , d'+n'≡d+n , refl) ,
                  (._ , (._ , (b , total-value-d'-b-n' , refl) , refl) , refl)) , refl) → {!(greedy-lemma d d' d'≤d n' n d'+n'≡d+n (Iso.from Fun (Refinement.i (FRefinement.comp (RSem' CoinBag'O) (ok (d' , n')))) (b , ?)))!} , {!!} } -- FRefinement.comp (RSem' CoinBag''O) (

{-

open GreedyTheorem (CoinBagD) R S R-transitive R-monotonic Q greedy-condition

solve : (c : Coin) (n : ℕ) → GreedySolution c n
solve c n = {!!}

-}
