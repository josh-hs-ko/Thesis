-- Solving the minimum coin change problem with the Greedy Theorem and algebraic ornamentation.
-- Several code fragments mysteriously make Agda hang, but should be type-correct.
-- These fragments are commented out and postulated.
-- Even so, this file can still take a long time to typecheck.

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

data CoinCompareView : Coin → Coin → Set where
  1p≤1p : CoinCompareView 1p 1p
  1p≤2p : CoinCompareView 1p 2p
  1p≤5p : CoinCompareView 1p 5p
  2p≤2p : CoinCompareView 2p 2p
  2p≤5p : CoinCompareView 2p 5p
  5p≤5p : CoinCompareView 5p 5p

compareCoin : (c d : Coin) → c ≤ d → CoinCompareView c d
compareCoin 1p 1p c≤d = 1p≤1p
compareCoin 1p 2p c≤d = 1p≤2p
compareCoin 1p 5p c≤d = 1p≤5p
compareCoin 2p 1p (s≤s ())
compareCoin 2p 2p c≤d = 2p≤2p
compareCoin 2p 5p c≤d = 2p≤5p
compareCoin 5p 1p (s≤s ())
compareCoin 5p 2p (s≤s (s≤s ()))
compareCoin 5p 5p c≤d = 5p≤5p


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

CoinBag'OD : OrnDesc (proj₁ ⋈ proj₁) pull CoinBagD
CoinBag'OD = ⌈ algOrn CoinBagD (fun⁺ total-value-alg) ⌉ ⊗ ⌈ algOrn CoinBagD (fun⁺ count-alg) ⌉

CoinBag'D : Desc (proj₁ ⋈ proj₁)
CoinBag'D = ⌊ CoinBag'OD ⌋

CoinBag'O : Orn pull CoinBagD CoinBag'D
CoinBag'O = ⌈ CoinBag'OD ⌉

CoinBag' : Coin → ℕ → ℕ → Set
CoinBag' c n l = μ CoinBag'D (ok (c , n) , ok (c , l))

nil' : {c : Coin} → CoinBag' c 0 0
nil' = con ((false , tt) , refl , (false , tt) , refl , refl , tt)

cons' : (d : Coin) → ∀ {c} → d ≤ c → ∀ {n n'} → value d + n ≡ n' → ∀ {l l'} → 1 + l ≡ l' → CoinBag' d n l → CoinBag' c n' l'
cons' d d≤c {n} {n'} eqn {l} {l'} eql b = con ((true , d , d≤c , n) , eqn , (true , d , d≤c , l) , eql , refl , refl , refl , b)

data CoinBag'View : {c : Coin} {n : ℕ} {l : ℕ} → CoinBag' c n l → Set where
  vnil  : {c : Coin} → CoinBag'View {c} {0} {0} nil'
  vcons : (d : Coin) {c : Coin} (d≤c : d ≤ c) {n l : ℕ} (b : CoinBag' d n l) → CoinBag'View {c} {value d + n} {1 + l} (cons' d d≤c refl refl b)

viewCoinBag' : ∀ {c n l} (b : CoinBag' c n l) → CoinBag'View b
viewCoinBag' (con ((false , _) , refl , (false , _) , refl , refl , _)) = vnil
viewCoinBag' (con ((false , _) , _ , (true , _) , _ , () , _))
viewCoinBag' (con ((true , _) , _ , (false , _) , _ , () , _))
viewCoinBag' (con ((true , d , d≤c , n) , refl , (.true , .d , .d≤c , l) , refl , refl , refl , refl , b)) = vcons d d≤c b

data CoinBag'View' : {c : Coin} {n : ℕ} {l : ℕ} → CoinBag' c n l → Set where
  empty : {c : Coin} → CoinBag'View' {c} {0} {0} nil'
  1p1p  : {m : ℕ} (lep : 1p ≤ 1p) {l : ℕ} (b : CoinBag' 1p m l) → CoinBag'View' {1p} {1 + m} {1 + l} (cons' 1p lep refl refl b)
  1p2p  : {m : ℕ} (lep : 1p ≤ 2p) {l : ℕ} (b : CoinBag' 1p m l) → CoinBag'View' {2p} {1 + m} {1 + l} (cons' 1p lep refl refl b)
  2p2p  : {m : ℕ} (lep : 2p ≤ 2p) {l : ℕ} (b : CoinBag' 2p m l) → CoinBag'View' {2p} {2 + m} {1 + l} (cons' 2p lep refl refl b)
  1p5p  : {m : ℕ} (lep : 1p ≤ 5p) {l : ℕ} (b : CoinBag' 1p m l) → CoinBag'View' {5p} {1 + m} {1 + l} (cons' 1p lep refl refl b)
  2p5p  : {m : ℕ} (lep : 2p ≤ 5p) {l : ℕ} (b : CoinBag' 2p m l) → CoinBag'View' {5p} {2 + m} {1 + l} (cons' 2p lep refl refl b)
  5p5p  : {m : ℕ} (lep : 5p ≤ 5p) {l : ℕ} (b : CoinBag' 5p m l) → CoinBag'View' {5p} {5 + m} {1 + l} (cons' 5p lep refl refl b)

view'CoinBag' : ∀ {c n l} (b : CoinBag' c n l) → CoinBag'View' b
view'CoinBag'     b  with viewCoinBag' b
view'CoinBag'     ._ | vnil = empty
view'CoinBag' {c} ._ | vcons  d  d≤c b with compareCoin d c d≤c
view'CoinBag'     ._ | vcons .1p d≤c b | 1p≤1p = 1p1p d≤c b
view'CoinBag'     ._ | vcons .1p d≤c b | 1p≤2p = 1p2p d≤c b
view'CoinBag'     ._ | vcons .1p d≤c b | 1p≤5p = 1p5p d≤c b
view'CoinBag'     ._ | vcons .2p d≤c b | 2p≤2p = 2p2p d≤c b
view'CoinBag'     ._ | vcons .2p d≤c b | 2p≤5p = 2p5p d≤c b
view'CoinBag'     ._ | vcons .5p d≤c b | 5p≤5p = 5p5p d≤c b

relax : {c : Coin} {n : ℕ} {l : ℕ} → (b : CoinBag' c n l) → ∀ {d} → c ≤ d → CoinBag' d n l
relax b  c≤d with viewCoinBag' b
relax ._ c≤d | vnil          = nil'
relax ._ c≤d | vcons e e≤c b = cons' e (≤ℕ-trans e≤c c≤d) refl refl b

insert1 : {c : Coin} {n : ℕ} {l : ℕ} → CoinBag' c n l → CoinBag' c (1 + n) (1 + l)
insert1      b  with viewCoinBag' b
insert1 {1p} ._ | vnil              = cons' 1p (s≤s z≤n) refl refl nil'
insert1 {2p} ._ | vnil              = cons' 1p (s≤s z≤n) refl refl nil'
insert1 {5p} ._ | vnil              = cons' 1p (s≤s z≤n) refl refl nil'
insert1      ._ | vcons d d≤c {n} b = cons' d d≤c (solve 2 (λ m vd → vd :+ (:con 1 :+ m) := :con 1 :+ (vd :+ m)) refl n (value d)) refl (insert1 b)

postulate
  greedy-lemma :
    (c d : Coin) → c ≤ d → (m n : ℕ) → value c + m ≡ value d + n → {l : ℕ} (b : CoinBag' c m l) → Σ[ l' ∶ ℕ ] CoinBag' d n l' × l' ≤ℕ l
{- [Proved.]
greedy-lemma  c   d  c≤d  m        n       eq       b  with compareCoin c d c≤d
greedy-lemma .1p .1p c≤d .n        n       refl {l} b  | 1p≤1p = l , b , ≤ℕ-refl
greedy-lemma .1p .2p c≤d .(1 + n)  n       refl     b  | 1p≤2p with view'CoinBag' b
greedy-lemma .1p .2p c≤d .(1 + n)  n       refl     ._ | 1p≤2p | 1p1p _ {l} b = l , relax b (s≤s z≤n) , z≤n {1} +-mono ≤ℕ-refl {l}
greedy-lemma .1p .5p c≤d .(4 + n)  n       refl     b  | 1p≤5p with view'CoinBag' b
greedy-lemma .1p .5p c≤d .(4 + n)  n       refl     ._ | 1p≤5p | 1p1p _ b  with view'CoinBag' b
greedy-lemma .1p .5p c≤d .(4 + n)  n       refl     ._ | 1p≤5p | 1p1p _ ._ | 1p1p _ b  with view'CoinBag' b
greedy-lemma .1p .5p c≤d .(4 + n)  n       refl     ._ | 1p≤5p | 1p1p _ ._ | 1p1p _ ._ | 1p1p _ b  with view'CoinBag' b
greedy-lemma .1p .5p c≤d .(4 + n)  n       refl     ._ | 1p≤5p | 1p1p _ ._ | 1p1p _ ._ | 1p1p _ ._ | 1p1p _ {l} b = l , relax b (s≤s z≤n) ,
                                                                                                                    z≤n {4} +-mono ≤ℕ-refl {l}
greedy-lemma .2p .2p c≤d .n        n       refl {l} b  | 2p≤2p = l , b , ≤ℕ-refl
greedy-lemma .2p .5p c≤d .(3 + n)  n       refl     b  | 2p≤5p with view'CoinBag' b
greedy-lemma .2p .5p c≤d .(3 + n)  n       refl     ._ | 2p≤5p | 1p2p _ b  with view'CoinBag' b
greedy-lemma .2p .5p c≤d .(3 + n)  n       refl     ._ | 2p≤5p | 1p2p _ ._ | 1p1p _ b  with view'CoinBag' b
greedy-lemma .2p .5p c≤d .(3 + n)  n       refl     ._ | 2p≤5p | 1p2p _ ._ | 1p1p _ ._ | 1p1p _ {l} b = l , relax b (s≤s z≤n) ,
                                                                                                        z≤n {3} +-mono ≤ℕ-refl {l}
greedy-lemma .2p .5p c≤d .(3 + n)  n       refl     ._ | 2p≤5p | 2p2p _ b  with view'CoinBag' b
greedy-lemma .2p .5p c≤d .(3 + n)  n       refl     ._ | 2p≤5p | 2p2p _ ._ | 1p2p _ {l} b = l , relax b (s≤s z≤n) , z≤n {2} +-mono ≤ℕ-refl {l}
greedy-lemma .2p .5p c≤d .(4 + m) .(1 + m) refl     ._ | 2p≤5p | 2p2p _ ._ | 2p2p {m} _ {l} b = 1 + l , relax (insert1 b) (s≤s (s≤s z≤n)) ,
                                                                                                z≤n {1} +-mono ≤ℕ-refl {1 + l}
greedy-lemma .5p .5p c≤d .n       n        refl {l} b  | 5p≤5p = l , b , ≤ℕ-refl
-}

greedy-condition-aux :
  (c : Coin) (ns : Ḟ CoinBagD (const ℕ) c) (b : CoinBag c) →
  ((α •⁺ Ṙ CoinBagD (foldR (fun⁺ total-value-alg) º⁺) •⁺ (Q ∩⁺ (fun⁺ total-value-alg º⁺ •⁺ fun⁺ total-value-alg)) º⁺) !!) c ns b →
  ((R º⁺ •⁺ α •⁺ Ṙ CoinBagD (foldR (fun⁺ total-value-alg) º⁺)) !!) c ns b
greedy-condition-aux c (false , _) ._ (._ , ((false , _) , (inj₁ refl , .0 , refl , refl) , _ , _ , refl) , refl) =
  nil , ((false , tt) , (tt , tt , refl) , refl) , (zero , (zero , refl , z≤n) , refl)
greedy-condition-aux c (false , _) ._ (_ , ((true  , _) , (inj₁ () , _) , _) , refl)
greedy-condition-aux c (false , _) ._ (_ , ((false , _) , (inj₂ () , _) , _) , refl)
greedy-condition-aux c (false , _) ._ (_ , ((true  , _) , (inj₂ (_ , _ , _ , ()) , _) , _) , refl)
greedy-condition-aux c (true  , _) ._ (_ , ((false , _) , (inj₁ () , _) , _) , refl)
greedy-condition-aux c (true  , _) ._ (_ , ((true  , _) , (inj₁ () , _) , _) , refl)
greedy-condition-aux c (true  , _) ._ (_ , ((false , _) , (inj₂ () , _) , _) , refl)
greedy-condition-aux c (true  , d , d≤c , n) ._
                       (._ , ((true  , d' , d'≤c , n') , (inj₂ (._ , d'≤d , ._ , refl) , ._ , d'+n'≡d+n , refl) ,
                              (._ , (._ , (b , total-value-d'-b-n' , refl) , refl) , refl)) , refl) =
  cons d d≤c (proj₁ better-solution) ,
  (_ , (_ , (_ , (_ , proj₁ (proj₂ better-solution) , refl) , refl) , refl) , refl) ,
  (1 + count (proj₁ better-solution) , (1 + count b , refl , s≤s better-evidence) , refl)
  where
    greedy-lemma-invocation : Σ[ l ∶ ℕ ] CoinBag' d n l × l ≤ℕ count b
    greedy-lemma-invocation =
      greedy-lemma d' d d'≤d n' n d'+n'≡d+n
         (Iso.from Fun (Refinement.i
            (FRefinement.comp
               (toFRefinement (⊗-FSwap ⌈ algOrn CoinBagD (fun⁺ total-value-alg) ⌉ ⌈ algOrn CoinBagD (fun⁺ count-alg) ⌉
                                       (algOrn-FSwap CoinBagD (fun⁺ total-value-alg)) (algOrn-FSwap CoinBagD (fun⁺ count-alg))))
               (ok (ok (d' , n') , ok (d' , count b)))))
            (b , total-value-d'-b-n' , modus-ponens-⊆⁺ (proj₁ (fun⁺-preserves-fold CoinBagD count-alg)) d' b (count b) refl))
    l : ℕ
    l = proj₁ greedy-lemma-invocation
    postulate better-solution : Σ[ b' ∶ CoinBag d ] foldR' (fun⁺ total-value-alg) d b' n × foldR' (fun⁺ count-alg) d b' l
{-  [Agda hangs here unexpectedly.]
    better-solution =
      Iso.to Fun (Refinement.i
        (FRefinement.comp
           (toFRefinement (⊗-FSwap ⌈ algOrn CoinBagD (fun⁺ total-value-alg) ⌉ ⌈ algOrn CoinBagD (fun⁺ count-alg) ⌉
                                   (algOrn-FSwap CoinBagD (fun⁺ total-value-alg)) (algOrn-FSwap CoinBagD (fun⁺ count-alg))))
           (ok (ok (d , n) , (ok (d , l))))))
        (proj₁ (proj₂ greedy-lemma-invocation))
-}
    postulate better-evidence : count (proj₁ better-solution) ≤ℕ count b
{-  [Agda hangs here unexpectedly.]
    better-evidence = ≤ℕ-trans (DecTotalOrder.reflexive ℕ-DecTotalOrder
                                 (modus-ponens-⊆⁺ (proj₂ (fun⁺-preserves-fold CoinBagD count-alg))
                                    d (proj₁ better-solution) l (proj₂ (proj₂ better-solution))))
                               (proj₂ (proj₂ greedy-lemma-invocation))
-}

greedy-condition :
  α •⁺ Ṙ CoinBagD (foldR (fun⁺ total-value-alg) º⁺) •⁺ (Q ∩⁺ (fun⁺ total-value-alg º⁺ •⁺ fun⁺ total-value-alg)) º⁺
    ⊆⁺ R º⁺ •⁺ α •⁺ Ṙ CoinBagD (foldR (fun⁺ total-value-alg) º⁺)
greedy-condition = wrap λ c → wrap (greedy-condition-aux c)

open GreedyTheorem (CoinBagD) R S R-transitive R-monotonic Q greedy-condition

{-

greedy : (c : Coin) (n : ℕ) → GreedySolution c n
greedy c n = {!!}

-}
