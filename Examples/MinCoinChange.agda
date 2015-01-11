-- Solving the minimum coin change problem with the Greedy Theorem and algebraic ornamentation.

module Examples.MinCoinChange where

open import Prelude.Category.Isomorphism
open import Prelude.Function
open import Prelude.InverseImage
open import Prelude.Function.Fam
open import Prelude.Preorder
open import Description
open import Ornament
open import Ornament.SequentialComposition
open import Ornament.ParallelComposition
open import Ornament.ParallelComposition.Swap
open import Ornament.RefinementSemantics
open import Ornament.Algebraic
open import Refinement
open import Relation
open import Relation.CompChain
open import Relation.Fold
open import Relation.Join
open import Relation.Meet
open import Relation.Minimum
import Relation.GreedyTheorem as GreedyTheorem
open import Examples.Nat using (ListTag; `nil; `cons)
open import Examples.List
open import Examples.List.Ordered

open import Function using (id; const; _∘_; flip; _on_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; z≤n; s≤s; _≤?_; _<_; _<′_) renaming (decTotalOrder to ℕ-DecTotalOrder)
open import Data.Nat.Properties using (m≤m+n; ¬i+1+j≤i; 1+n≰n; ≤⇒≤′; ≰⇒>; _+-mono_; module SemiringSolver)
open Data.Nat.Properties.SemiringSolver renaming (con to :con)
open import Data.Product using (Σ; Σ-syntax; _,_; proj₁; proj₂; _×_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary using (module DecTotalOrder)
import Relation.Binary.PreorderReasoning as PreorderReasoning
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; _≢_)
open import Induction.Nat using (<-rec)


-- Natural numbers provided by the standard library are used
-- so various properties already proved in the standard library
-- do not need to be proved again (tediously) for the natural
-- numbers from Examples.Nat.

≤-refl : {x : ℕ} → x ≤ x
≤-refl = DecTotalOrder.refl ℕ-DecTotalOrder

≤-trans : ∀ {x y z} → x ≤ y → y ≤ z → x ≤ z
≤-trans = DecTotalOrder.trans ℕ-DecTotalOrder

≤-reflexive : ∀ {x y} → x ≡ y → x ≤ y
≤-reflexive = DecTotalOrder.reflexive ℕ-DecTotalOrder


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

_≤C_ : Coin → Coin → Set
_≤C_ = _≤_ on value

1p-minimum : (c : Coin) → 1p ≤C c
1p-minimum 1p = ≤-refl
1p-minimum 2p = s≤s z≤n
1p-minimum 5p = s≤s z≤n

5p-maximum : (c : Coin) → c ≤C 5p
5p-maximum 1p = s≤s z≤n
5p-maximum 2p = s≤s (s≤s z≤n)
5p-maximum 5p = ≤-refl

coin-above-zero : (c : Coin) → 0 < value c
coin-above-zero 1p = s≤s z≤n
coin-above-zero 2p = s≤s z≤n
coin-above-zero 5p = s≤s z≤n

data CoinOrderedView : Coin → Coin → Set where
  1p1p : CoinOrderedView 1p 1p
  1p2p : CoinOrderedView 1p 2p
  1p5p : CoinOrderedView 1p 5p
  2p2p : CoinOrderedView 2p 2p
  2p5p : CoinOrderedView 2p 5p
  5p5p : CoinOrderedView 5p 5p

view-ordered-coin : (c d : Coin) → c ≤C d → CoinOrderedView c d
view-ordered-coin 1p 1p c≤d = 1p1p
view-ordered-coin 1p 2p c≤d = 1p2p
view-ordered-coin 1p 5p c≤d = 1p5p
view-ordered-coin 2p 1p (s≤s ())
view-ordered-coin 2p 2p c≤d = 2p2p
view-ordered-coin 2p 5p c≤d = 2p5p
view-ordered-coin 5p 1p (s≤s ())
view-ordered-coin 5p 2p (s≤s (s≤s ()))
view-ordered-coin 5p 5p c≤d = 5p5p


--------
-- coin bags as sorted coin lists

CoinBagOD : OrnDesc Coin ! ⌊ ListOD Coin ⌋
CoinBagOD = OrdListOD Coin (flip _≤C_)

CoinBagD : Desc Coin
CoinBagD = ⌊ CoinBagOD ⌋

CoinBagO : Orn ! ⌊ ListOD Coin ⌋ CoinBagD
CoinBagO = ⌈ CoinBagOD ⌉

CoinBag : Coin → Set
CoinBag = μ CoinBagD

nil : {c : Coin} → CoinBag c
nil = con (`nil , tt)

cons : (d : Coin) → {c : Coin} → d ≤C c → CoinBag d → CoinBag c
cons d d≤c b = con (`cons , d , d≤c , b , tt)

total-value-alg : Ḟ CoinBagD (const ℕ) ⇉ const ℕ
total-value-alg (`nil  ,             _) = 0
total-value-alg (`cons , c , _ , m , _) = value c + m

total-value : ∀ {c} → CoinBag c → ℕ
total-value = fold total-value-alg

count-alg : Ḟ CoinBagD (const ℕ) ⇉ const ℕ
count-alg (`nil  ,             _) = 0
count-alg (`cons , _ , _ , m , _) = 1 + m

count : ∀ {c} → CoinBag c → ℕ
count = fold count-alg


--------
-- specification

leq-ℕ : const {B = Coin} ℕ ↝ const ℕ
leq-ℕ = wrap (const (flip _≤_))

leq-ℕ-reflexive : idR ⊆ leq-ℕ
leq-ℕ-reflexive = wrap λ c → wrap λ { x .x refl → ≤-refl }

leq-ℕ-transitive : leq-ℕ • leq-ℕ ⊆ leq-ℕ
leq-ℕ-transitive = wrap (const (wrap λ { x y (z , z≤x , y≤z) → ≤-trans y≤z z≤x }))

R : CoinBag ↝ CoinBag
R = fun count º • leq-ℕ • fun count

R-transitive : R • R ⊆ R
R-transitive =
  begin
    (fun count º • leq-ℕ • fun count) • (fun count º • leq-ℕ • fun count)
      ⊆⟨ proj₁ (chain-normalise
                  (([ fun count º ] ▪ [ leq-ℕ ] ▪ [ fun count ]) ▪ ([ fun count º ] ▪ [ leq-ℕ ] ▪ [ fun count ]))) ⟩
    fun count º • leq-ℕ • fun count • fun count º • leq-ℕ • fun count
      ⊆⟨ ⊆-chain (fun count º ▪ leq-ℕ ◇) (fun count ▪ fun count º ◇) (idR ◇) (fun-simple count) ⟩
    fun count º • leq-ℕ • idR • leq-ℕ • fun count
      ⊆⟨ ⊆-chain (fun count º ◇) (leq-ℕ ▪ idR ◇) (leq-ℕ ◇) (proj₁ (idR-r leq-ℕ)) ⟩
    fun count º • leq-ℕ • leq-ℕ • fun count
      ⊆⟨ ⊆-chain (fun count º ◇) (leq-ℕ ▪ leq-ℕ ◇) (leq-ℕ ◇) leq-ℕ-transitive ⟩
    fun count º • leq-ℕ • fun count
  □
  where open PreorderReasoning (⊆-Preorder CoinBag CoinBag) renaming (_∼⟨_⟩_ to _⊆⟨_⟩_; _∎ to _□)

S : Ḟ CoinBagD (const ℕ) ↝ const ℕ
S = fun total-value-alg


--------
-- Monotonicity

count-alg-monotonic : fun count-alg • Ṙ CoinBagD leq-ℕ ⊆ leq-ℕ • fun count-alg
count-alg-monotonic =
  wrap λ c → wrap λ { (`nil  ,               _) ._ (._ , (_ , _ , refl) , refl) → 0 , refl , ≤-refl
                    ; (`cons , d , d≤c , n , _) ._ (._ , (._ , (._ , (._ , (m , m≤n , _ , _ , refl) , refl) , refl) , refl) , refl) →
                        1 + n , refl , ≤-refl {1} +-mono m≤n }

R-monotonic-lemma :
  (R' : const {B = Coin} ℕ ↝ const ℕ) → (fun count-alg • Ṙ CoinBagD R' ⊆ R' • fun count-alg) →
  fun count-alg • Ṙ CoinBagD R' • Ṙ CoinBagD (fun count) • α º ⊆ R' • fun count
R-monotonic-lemma R' monotonicity =
  begin
    fun count-alg • Ṙ CoinBagD R' • Ṙ CoinBagD (fun count) • α º
      ⊆⟨ ⊆-chain-r (fun count-alg ▪ Ṙ CoinBagD R' ◇) (R' ▪ fun count-alg ◇) monotonicity ⟩
    R' • fun count-alg • Ṙ CoinBagD (fun count) • α º
      ⊆⟨ ⊆-chain (R' ▪ fun count-alg ◇) (Ṙ CoinBagD (fun count) ◇) (Ṙ CoinBagD (foldR (fun count-alg)) ◇)
            (Ṙ-monotonic CoinBagD (proj₁ (fun-preserves-fold CoinBagD count-alg))) ⟩
    R' • fun count-alg • Ṙ CoinBagD (foldR (fun count-alg)) • α º
      ⊆⟨ •-monotonic-l R' (proj₂ (foldR-computation' CoinBagD (fun count-alg))) ⟩
    R' • foldR (fun count-alg)
      ⊆⟨ •-monotonic-l R' (proj₂ (fun-preserves-fold CoinBagD count-alg)) ⟩
    R' • fun count
  □
  where open PreorderReasoning (⊆-Preorder (μ CoinBagD) (const ℕ)) renaming (_∼⟨_⟩_ to _⊆⟨_⟩_; _∎ to _□)

R-monotonic : α • Ṙ CoinBagD R • α º ⊆ R
R-monotonic = 
  begin
    α • Ṙ CoinBagD (fun count º • leq-ℕ • fun count) • α º
      ⊆⟨ ⊆-chain (α ◇) (Ṙ CoinBagD (fun count º • leq-ℕ • fun count) ◇)
            (Ṙ CoinBagD (fun count º) ▪ Ṙ CoinBagD leq-ℕ ▪ Ṙ CoinBagD (fun count) ◇)
            (proj₁ (Ṙ-chain CoinBagD (fun count º ▪ leq-ℕ ▪ fun count ◇))) ⟩
    α • Ṙ CoinBagD (fun count º) • Ṙ CoinBagD leq-ℕ • Ṙ CoinBagD (fun count) • α º
      ⊆⟨ ⊆-chain (α ▪ Ṙ CoinBagD (fun count º) ◇)
            (Ṙ CoinBagD leq-ℕ ◇) (Ṙ CoinBagD (leq-ℕ • idR) ◇)
            (Ṙ-monotonic CoinBagD (proj₂ (idR-r leq-ℕ))) ⟩
    α • Ṙ CoinBagD (fun count º) • Ṙ CoinBagD (leq-ℕ • idR) • Ṙ CoinBagD (fun count) • α º
      ⊆⟨ ⊆-chain (α ▪ Ṙ CoinBagD (fun count º) ◇)
            (Ṙ CoinBagD (leq-ℕ • idR) ◇) (Ṙ CoinBagD (leq-ℕ • leq-ℕ) ◇)
            (Ṙ-monotonic CoinBagD (•-monotonic-l leq-ℕ leq-ℕ-reflexive)) ⟩
    α • Ṙ CoinBagD (fun count º) • Ṙ CoinBagD (leq-ℕ • leq-ℕ) • Ṙ CoinBagD (fun count) • α º
      ⊆⟨ ⊆-chain (α ▪ Ṙ CoinBagD (fun count º) ◇)
            (Ṙ CoinBagD (leq-ℕ • leq-ℕ) ◇) (Ṙ CoinBagD leq-ℕ ▪ Ṙ CoinBagD leq-ℕ ◇)
            (proj₁ (Ṙ-preserves-comp CoinBagD leq-ℕ leq-ℕ)) ⟩
    α • Ṙ CoinBagD (fun count º) • Ṙ CoinBagD leq-ℕ • Ṙ CoinBagD leq-ℕ • Ṙ CoinBagD (fun count) • α º
      ⊆⟨ ⊆-chain-l (α ▪ Ṙ CoinBagD (fun count º) ▪ Ṙ CoinBagD leq-ℕ ◇)
            (proj₂ (idR-l (Ṙ CoinBagD leq-ℕ • Ṙ CoinBagD (fun count) • α º))) ⟩
    α • Ṙ CoinBagD (fun count º) • Ṙ CoinBagD leq-ℕ • idR • Ṙ CoinBagD leq-ℕ • Ṙ CoinBagD (fun count) • α º
      ⊆⟨ ⊆-chain (α ▪ Ṙ CoinBagD (fun count º) ▪ Ṙ CoinBagD leq-ℕ ◇)
            (idR ◇) (fun count-alg º ▪ fun count-alg ◇)
            (fun-entire count-alg) ⟩
    α • Ṙ CoinBagD (fun count º) • Ṙ CoinBagD leq-ℕ • fun count-alg º •
    fun count-alg • Ṙ CoinBagD leq-ℕ • Ṙ CoinBagD (fun count) • α º
      ⊆⟨ ⊆-chain (α ◇) (Ṙ CoinBagD (fun count º) ◇)
            (Ṙ CoinBagD (fun count) º ◇)
            (proj₁ (Ṙ-preserves-conv CoinBagD (fun count))) ⟩
    α • Ṙ CoinBagD (fun count) º • Ṙ CoinBagD leq-ℕ • fun count-alg º •
    fun count-alg • Ṙ CoinBagD leq-ℕ • Ṙ CoinBagD (fun count) • α º
      ⊆⟨ ⊆-chain (α ▪ Ṙ CoinBagD (fun count) º ◇)
            (Ṙ CoinBagD leq-ℕ ◇) (Ṙ CoinBagD (leq-ℕ º) º ◇)
            (proj₁ (Ṙ-preserves-conv CoinBagD (leq-ℕ º))) ⟩
    α • Ṙ CoinBagD (fun count) º • Ṙ CoinBagD (leq-ℕ º) º • fun count-alg º •
    fun count-alg • Ṙ CoinBagD leq-ℕ • Ṙ CoinBagD (fun count) • α º
      ⊆⟨ ⊆-chain-r
            (α ▪ Ṙ CoinBagD (fun count) º ▪ Ṙ CoinBagD (leq-ℕ º) º ▪ fun count-alg º ◇)
            ((fun count-alg • Ṙ CoinBagD (leq-ℕ º) • Ṙ CoinBagD (fun count) • α º) º ◇)
            (proj₂ (º-chain (fun count-alg ▪ Ṙ CoinBagD (leq-ℕ º) ▪ Ṙ CoinBagD (fun count) ▪ α º ◇))) ⟩
    (fun count-alg • Ṙ CoinBagD (leq-ℕ º) • Ṙ CoinBagD (fun count) • α º) º •
     fun count-alg • Ṙ CoinBagD  leq-ℕ     • Ṙ CoinBagD (fun count) • α º
      ⊆⟨ •-monotonic (º-monotonic (R-monotonic-lemma (leq-ℕ º) (fun-monotonic-alg-lemma CoinBagD count-alg leq-ℕ count-alg-monotonic)))
                      (R-monotonic-lemma leq-ℕ count-alg-monotonic) ⟩
    (leq-ℕ º • fun count) º • leq-ℕ • fun count
      ⊆⟨ ⊆-chain-r ((leq-ℕ º • fun count) º ◇) (fun count º ▪ leq-ℕ ◇) (proj₁ (º-preserves-comp (leq-ℕ º) (fun count))) ⟩
    fun count º • leq-ℕ • leq-ℕ • fun count
      ⊆⟨ ⊆-chain (fun count º ◇) (leq-ℕ ▪ leq-ℕ ◇) (leq-ℕ ◇) leq-ℕ-transitive ⟩
    fun count º • leq-ℕ • fun count
  □
  where open PreorderReasoning (⊆-Preorder CoinBag CoinBag) renaming (_∼⟨_⟩_ to _⊆⟨_⟩_; _∎ to _□)


--------
-- Greedy condition

Q : Ḟ CoinBagD (const ℕ) ↝ Ḟ CoinBagD (const ℕ)
Q = wrap λ { c (`nil   ,     _) → return (`nil , tt)
           ; c (`cons  , d , _) → (_≤C_ d) >>= λ e → any>>= λ r → return (`cons , e , r) }

CoinBag'OD : OrnDesc (proj₁ ⋈ proj₁) pull CoinBagD
CoinBag'OD = ⌈ algOrn CoinBagD (fun total-value-alg) ⌉ ⊗ ⌈ algOrn CoinBagD (fun count-alg) ⌉

CoinBag'D : Desc (proj₁ ⋈ proj₁)
CoinBag'D = ⌊ CoinBag'OD ⌋

CoinBag'O : Orn pull CoinBagD CoinBag'D
CoinBag'O = ⌈ CoinBag'OD ⌉

CoinBag' : Coin → ℕ → ℕ → Set
CoinBag' c n l = μ CoinBag'D (ok (c , n) , ok (c , l))

nil' : {c : Coin} → CoinBag' c 0 0
nil' = con (`nil , tt , refl , tt , refl , tt)

cons' : (d : Coin) → ∀ {c} → d ≤C c → ∀ {n n'} → value d + n ≡ n' → ∀ {l l'} → 1 + l ≡ l' → CoinBag' d n l → CoinBag' c n' l'
cons' d d≤c {n} {n'} eqn {l} {l'} eql b = con (`cons , d , d≤c , (n , tt) , eqn , (l , tt) , eql , b , tt)

data CoinBag'View : {c : Coin} {n : ℕ} {l : ℕ} → CoinBag' c n l → Set where
  vnil  : {c : Coin} → CoinBag'View {c} {0} {0} nil'
  vcons : (d : Coin) {c : Coin} (d≤c : d ≤C c) {n l : ℕ} (b : CoinBag' d n l) → CoinBag'View {c} {value d + n} {1 + l} (cons' d d≤c refl refl b)

viewCoinBag' : ∀ {c n l} (b : CoinBag' c n l) → CoinBag'View b
viewCoinBag' (con (`nil  , _ , refl , _ , refl , _)) = vnil
viewCoinBag' (con (`cons , d , d≤c , (n , _) , refl , (l , _) , refl , b , _)) = vcons d d≤c b

data CoinBag'View' : {c : Coin} {n : ℕ} {l : ℕ} → CoinBag' c n l → Set where
  empty : {c : Coin} → CoinBag'View' {c} {0} {0} nil'
  1p1p  : {m : ℕ} (lep : 1p ≤C 1p) {l : ℕ} (b : CoinBag' 1p m l) → CoinBag'View' {1p} {1 + m} {1 + l} (cons' 1p lep refl refl b)
  1p2p  : {m : ℕ} (lep : 1p ≤C 2p) {l : ℕ} (b : CoinBag' 1p m l) → CoinBag'View' {2p} {1 + m} {1 + l} (cons' 1p lep refl refl b)
  2p2p  : {m : ℕ} (lep : 2p ≤C 2p) {l : ℕ} (b : CoinBag' 2p m l) → CoinBag'View' {2p} {2 + m} {1 + l} (cons' 2p lep refl refl b)
  1p5p  : {m : ℕ} (lep : 1p ≤C 5p) {l : ℕ} (b : CoinBag' 1p m l) → CoinBag'View' {5p} {1 + m} {1 + l} (cons' 1p lep refl refl b)
  2p5p  : {m : ℕ} (lep : 2p ≤C 5p) {l : ℕ} (b : CoinBag' 2p m l) → CoinBag'View' {5p} {2 + m} {1 + l} (cons' 2p lep refl refl b)
  5p5p  : {m : ℕ} (lep : 5p ≤C 5p) {l : ℕ} (b : CoinBag' 5p m l) → CoinBag'View' {5p} {5 + m} {1 + l} (cons' 5p lep refl refl b)

view'CoinBag' : ∀ {c n l} (b : CoinBag' c n l) → CoinBag'View' b
view'CoinBag'     b  with viewCoinBag' b
view'CoinBag'     ._ | vnil = empty
view'CoinBag' {c} ._ | vcons  d  d≤c b with view-ordered-coin d c d≤c
view'CoinBag'     ._ | vcons .1p d≤c b | 1p1p = 1p1p d≤c b
view'CoinBag'     ._ | vcons .1p d≤c b | 1p2p = 1p2p d≤c b
view'CoinBag'     ._ | vcons .1p d≤c b | 1p5p = 1p5p d≤c b
view'CoinBag'     ._ | vcons .2p d≤c b | 2p2p = 2p2p d≤c b
view'CoinBag'     ._ | vcons .2p d≤c b | 2p5p = 2p5p d≤c b
view'CoinBag'     ._ | vcons .5p d≤c b | 5p5p = 5p5p d≤c b

relax : {c : Coin} {n : ℕ} {l : ℕ} → (b : CoinBag' c n l) → ∀ {d} → c ≤C d → CoinBag' d n l
relax b  c≤d with viewCoinBag' b
relax ._ c≤d | vnil          = nil'
relax ._ c≤d | vcons e e≤c b = cons' e (≤-trans e≤c c≤d) refl refl b

insert1 : {c : Coin} {n : ℕ} {l : ℕ} → CoinBag' c n l → CoinBag' c (1 + n) (1 + l)
insert1     b  with viewCoinBag' b
insert1 {c} ._ | vnil              = cons' 1p (1p-minimum c) refl refl nil'
insert1     ._ | vcons d d≤c {n} b = cons' d d≤c (solve 2 (λ m vd → vd :+ (:con 1 :+ m) := :con 1 :+ (vd :+ m)) refl n (value d)) refl (insert1 b)

greedy-lemma :
  (c d : Coin) → c ≤C d → (m n : ℕ) → value c + m ≡ value d + n → {l : ℕ} (b : CoinBag' c m l) → Σ[ l' ∈ ℕ ] CoinBag' d n l' × l' ≤ l
greedy-lemma  c   d  c≤d  m        n       eq       b  with view-ordered-coin c d c≤d
greedy-lemma .1p .1p c≤d .n        n       refl {l} b  | 1p1p = l , b , ≤-refl
greedy-lemma .1p .2p c≤d .(1 + n)  n       refl     b  | 1p2p with view'CoinBag' b
greedy-lemma .1p .2p c≤d .(1 + n)  n       refl     ._ | 1p2p | 1p1p _ {l} b = l , relax b (s≤s z≤n) , z≤n {1} +-mono ≤-refl {l}
greedy-lemma .1p .5p c≤d .(4 + n)  n       refl     b  | 1p5p with view'CoinBag' b
greedy-lemma .1p .5p c≤d .(4 + n)  n       refl     ._ | 1p5p | 1p1p _ b  with view'CoinBag' b
greedy-lemma .1p .5p c≤d .(4 + n)  n       refl     ._ | 1p5p | 1p1p _ ._ | 1p1p _ b  with view'CoinBag' b
greedy-lemma .1p .5p c≤d .(4 + n)  n       refl     ._ | 1p5p | 1p1p _ ._ | 1p1p _ ._ | 1p1p _ b  with view'CoinBag' b
greedy-lemma .1p .5p c≤d .(4 + n)  n       refl     ._ | 1p5p | 1p1p _ ._ | 1p1p _ ._ | 1p1p _ ._ | 1p1p _ {l} b = l , relax b (s≤s z≤n) ,
                                                                                                                   z≤n {4} +-mono ≤-refl {l}
greedy-lemma .2p .2p c≤d .n        n       refl {l} b  | 2p2p = l , b , ≤-refl
greedy-lemma .2p .5p c≤d .(3 + n)  n       refl     b  | 2p5p with view'CoinBag' b
greedy-lemma .2p .5p c≤d .(3 + n)  n       refl     ._ | 2p5p | 1p2p _ b  with view'CoinBag' b
greedy-lemma .2p .5p c≤d .(3 + n)  n       refl     ._ | 2p5p | 1p2p _ ._ | 1p1p _ b  with view'CoinBag' b
greedy-lemma .2p .5p c≤d .(3 + n)  n       refl     ._ | 2p5p | 1p2p _ ._ | 1p1p _ ._ | 1p1p _ {l} b = l , relax b (s≤s z≤n) ,
                                                                                                       z≤n {3} +-mono ≤-refl {l}
greedy-lemma .2p .5p c≤d .(3 + n)  n       refl     ._ | 2p5p | 2p2p _ b  with view'CoinBag' b
greedy-lemma .2p .5p c≤d .(3 + n)  n       refl     ._ | 2p5p | 2p2p _ ._ | 1p2p _ {l} b = l , relax b (s≤s z≤n) , z≤n {2} +-mono ≤-refl {l}
greedy-lemma .2p .5p c≤d .(4 + m) .(1 + m) refl     ._ | 2p5p | 2p2p _ ._ | 2p2p {m} _ {l} b = 1 + l , relax (insert1 b) (s≤s (s≤s z≤n)) ,
                                                                                               z≤n {1} +-mono ≤-refl {1 + l}
greedy-lemma .5p .5p c≤d .n       n        refl {l} b  | 5p5p = l , b , ≤-refl

greedy-condition-aux :
  (c : Coin) (ns : Ḟ CoinBagD (const ℕ) c) (b : CoinBag c) →
  ((α • Ṙ CoinBagD (foldR (fun total-value-alg) º) • (Q ∩ (fun total-value-alg º • fun total-value-alg)) º) !!) c ns b →
  ((R º • α • Ṙ CoinBagD (foldR (fun total-value-alg) º)) !!) c ns b
greedy-condition-aux c (`nil , _) ._ (._ , ((`nil , _) , (refl , ._ , refl , refl) , _ , _ , refl) , refl) =
  nil , ((`nil , tt) , (tt , tt , refl) , refl) , (zero , (zero , refl , z≤n) , refl)
greedy-condition-aux c (`nil , _) ._ ( _ , ((`cons  , _) , ((_ , _ , _ , ()) , _) , _) , refl)
greedy-condition-aux c (`cons  , _) ._ ( _ , ((`nil , _) , (() , _) , _) , refl)
greedy-condition-aux c (`cons  , d , d≤c , n , tt) ._
                       (._ , ((`cons  , d' , d'≤c , n' , tt) , ((._ , d'≤d , ._ , refl) , ._ , d'+n'≡d+n , refl) ,
                              ._ , (._ , ((b , _) , (._ , total-value-d'-b-n' , _ , _ , refl) , refl) , refl) , refl) , refl) =
  cons d d≤c (proj₁ better-solution) ,
  (_ , (_ , ((d≤c , proj₁ better-solution , tt) ,
             (_ , (proj₁ better-solution , proj₁ (proj₂ better-solution) , tt , tt , refl) , refl) , refl) , refl) , refl) ,
  _ , (_ , refl , s≤s better-evidence) , refl
  where
    greedy-lemma-invocation : Σ[ l ∈ ℕ ] CoinBag' d n l × l ≤ count b
    greedy-lemma-invocation =
      greedy-lemma d' d d'≤d n' n d'+n'≡d+n
         (Iso.from (Refinement.i
            (FRefinement.comp
               (toFRefinement (⊗-FSwap ⌈ algOrn CoinBagD (fun total-value-alg) ⌉ ⌈ algOrn CoinBagD (fun count-alg) ⌉
                                       (algOrn-FSwap CoinBagD (fun total-value-alg)) (algOrn-FSwap CoinBagD (fun count-alg))))
               (ok (ok (d' , n') , ok (d' , count b)))))
            (b , total-value-d'-b-n' , modus-ponens-⊆ (proj₁ (fun-preserves-fold CoinBagD count-alg)) d' b (count b) refl))
    l : ℕ
    l = proj₁ greedy-lemma-invocation
    better-solution : Σ[ b' ∈ CoinBag d ] foldR' (fun total-value-alg) d b' n × foldR' (fun count-alg) d b' l
    better-solution =
      Iso.to (Refinement.i
        (FRefinement.comp
           (toFRefinement (⊗-FSwap ⌈ algOrn CoinBagD (fun total-value-alg) ⌉ ⌈ algOrn CoinBagD (fun count-alg) ⌉
                                   (algOrn-FSwap CoinBagD (fun total-value-alg)) (algOrn-FSwap CoinBagD (fun count-alg))))
           (ok (ok (d , n) , (ok (d , l))))))
        (proj₁ (proj₂ greedy-lemma-invocation))
    better-evidence : count (proj₁ better-solution) ≤ count b
    better-evidence = ≤-trans (DecTotalOrder.reflexive ℕ-DecTotalOrder
                                 (modus-ponens-⊆ (proj₂ (fun-preserves-fold CoinBagD count-alg))
                                    d (proj₁ better-solution) l (proj₂ (proj₂ better-solution))))
                              (proj₂ (proj₂ greedy-lemma-invocation))

greedy-condition :
  α • Ṙ CoinBagD (foldR (fun total-value-alg) º) • (Q ∩ (fun total-value-alg º • fun total-value-alg)) º
    ⊆ R º • α • Ṙ CoinBagD (foldR (fun total-value-alg) º)
greedy-condition = wrap λ c → wrap (greedy-condition-aux c)


--------
-- Greedy solution

open GreedyTheorem CoinBagD R S R-transitive R-monotonic Q greedy-condition

coin-above-zero-lemma : ∀ d {k} → value d + k ≢ 0
coin-above-zero-lemma d eq = 1+n≰n (≤-trans (coin-above-zero d) (≤-trans (m≤m+n (value d) _) (≤-reflexive eq)))

gnil : ∀ {c} → GreedySolution c 0
gnil = con (`nil , tt , (refl , (λ { (`nil , _) _ → refl
                                   ; (`cons , d , _) eq → ⊥-elim (coin-above-zero-lemma d eq) })) , tt)

UsableCoin : ℕ → Coin → Coin → Set
UsableCoin n c d = (d ≤C c) × (Σ[ n' ∈ ℕ ] value d + n' ≡ n)

gcons : (d : Coin) → ∀ {c} → d ≤C c → ∀ {n'} → ((e : Coin) → UsableCoin (value d + n') c e → e ≤C d) →
        GreedySolution d n' → GreedySolution c (value d + n')
gcons d d≤c {n'} guc g =
  con (`cons , d , d≤c , (n' , tt) , (refl , (λ { (`nil , _) eq → ⊥-elim (coin-above-zero-lemma d (sym eq))
                                                ; (`cons , e , e≤c , m , _) eq → d , guc e (e≤c , m , eq) , (d≤c , n' , tt) , refl })) , g , tt)

data AtLeastView : ℕ → ℕ → Set where
  at-least  : (m : ℕ) (n : ℕ)    → AtLeastView m (m + n)
  less-than : {m n : ℕ} → n < m → AtLeastView m n

at-least-view : (m n : ℕ) → AtLeastView m n
at-least-view zero    n = at-least zero n
at-least-view (suc m) zero = less-than (s≤s z≤n)
at-least-view (suc m) (suc  n       ) with at-least-view m n
at-least-view (suc m) (suc .(m + n')) | at-least .m n' = at-least (suc m) n'
at-least-view (suc m) (suc  n       ) | less-than n<m  = less-than (s≤s n<m)

try-1p : (n : ℕ) → 0 < n → Σ[ d ∈ Coin ] UsableCoin n 1p d × ((e : Coin) → UsableCoin n 1p e → e ≤C d)
try-1p  n       0<n with at-least-view 1 n
try-1p .(1 + n) 0<n | at-least .1 n = 1p , (≤-refl , n , refl) , 1p-greatest
  where 1p-greatest : (e : Coin) → UsableCoin (1 + n) 1p e → e ≤C 1p
        1p-greatest  e  (e≤1p , n' , eq) with view-ordered-coin e 1p e≤1p
        1p-greatest .1p (e≤1p , n' , eq) | 1p1p = ≤-refl
try-1p .0       ()  | less-than (s≤s z≤n)

try-2p : (n : ℕ) → 0 < n → Σ[ d ∈ Coin ] UsableCoin n 2p d × ((e : Coin) → UsableCoin n 2p e → e ≤C d)
try-2p  n       0<n with at-least-view 2 n
try-2p .(2 + n) 0<n | at-least .2 n = 2p , (≤-refl , n , refl) , 2p-greatest
  where 2p-greatest : (e : Coin) → UsableCoin (2 + n) 2p e → e ≤C 2p
        2p-greatest  e  (e≤2p , n' , eq) = e≤2p
try-2p  n       0<n | less-than n<2 with try-1p n 0<n
try-2p  n       0<n | less-than n<2 | d , (lep , n' , eq) , d-greatest = d , (≤-trans lep (s≤s z≤n) , n' , eq) , 2p-greatest
  where 2p-greatest : (e : Coin) → UsableCoin n 2p e → e ≤C d
        2p-greatest  e  (e≤2p , n' , eq) with view-ordered-coin e 2p e≤2p
        2p-greatest .1p (e≤2p , n' , eq) | 1p2p = d-greatest 1p (≤-refl , n' , eq)
        2p-greatest .2p (e≤2p , n' , eq) | 2p2p = ⊥-elim (¬i+1+j≤i 2 (≤-trans (s≤s (≤-reflexive eq)) n<2))

try-5p : (n : ℕ) → 0 < n → Σ[ d ∈ Coin ] UsableCoin n 5p d × ((e : Coin) → UsableCoin n 5p e → e ≤C d)
try-5p  n       0<n with at-least-view 5 n
try-5p .(5 + n) 0<n | at-least .5 n = 5p , (≤-refl , n , refl) , 5p-greatest
  where 5p-greatest : (e : Coin) → UsableCoin (5 + n) 5p e → e ≤C 5p
        5p-greatest  e  (e≤5p , n' , eq) = e≤5p
try-5p  n       0<n | less-than n<5 with try-2p n 0<n
try-5p  n       0<n | less-than n<5 | d , (lep , n' , eq) , d-greatest = d , (≤-trans lep (s≤s (s≤s z≤n)) , n' , eq) , 5p-greatest
  where 5p-greatest : (e : Coin) → UsableCoin n 5p e → e ≤C d
        5p-greatest  e  (e≤5p , n' , eq) with view-ordered-coin e 5p e≤5p
        5p-greatest .1p (e≤5p , n' , eq) | 1p5p = d-greatest 1p (s≤s z≤n , n' , eq)
        5p-greatest .2p (e≤5p , n' , eq) | 2p5p = d-greatest 2p (≤-refl , n' , eq)
        5p-greatest .5p (e≤5p , n' , eq) | 5p5p = ⊥-elim (¬i+1+j≤i 5 (≤-trans (s≤s (≤-reflexive eq)) n<5))

maximum-coin : (n : ℕ) → 0 < n → (c : Coin) → Σ[ d ∈ Coin ] UsableCoin n c d × ((e : Coin) → UsableCoin n c e → e ≤C d)
maximum-coin n 0<n 1p = try-1p n 0<n
maximum-coin n 0<n 2p = try-2p n 0<n
maximum-coin n 0<n 5p = try-5p n 0<n

-- NB: should be able to generalise the program structure of maximum-coin to work on lists of coins

data ZeroView : ℕ → Set where
  is-zero    : ZeroView 0
  above-zero : {n : ℕ} → 0 < n → ZeroView n

compare-with-zero : (n : ℕ) → ZeroView n
compare-with-zero  n with n ≤? 0
compare-with-zero .0 | yes z≤n = is-zero
compare-with-zero  n | no  n≰0 = above-zero (≰⇒> n≰0)

greedy : (c : Coin) (n : ℕ) → GreedySolution c n
greedy c n = <-rec P f n c
  where
    P : ℕ → Set
    P n = ∀ c → GreedySolution c n
    f : (n : ℕ) → ((n' : ℕ) → n' <′ n → P n') → P n
    f  n rec c with compare-with-zero n
    f .0 rec c | is-zero = gnil
    f  n rec c | above-zero 0<n with maximum-coin n 0<n c
    f ._ rec c | above-zero 0<n | d , (d≤c , n' , refl) , guc = gcons d d≤c guc (rec n' (≤⇒≤′ (coin-above-zero d +-mono ≤-refl {n'})) d)

greedy-correctness : (n : ℕ) → ((min R •Λ (foldR S º)) !!) 5p n (forget ⌈ GreedySolutionOD ⌉ (greedy 5p n))
greedy-correctness n = optimisation-proof 5p n (greedy 5p n)
