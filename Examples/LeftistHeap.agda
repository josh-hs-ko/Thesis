-- The ordering property and balancing properties of leftist heaps are treated separately when needed.

open import Data.Product using (Σ; Σ-syntax; _,_; proj₁; proj₂; _×_) renaming (map to _**_)
open import Relation.Nullary using (¬_; Dec; yes; no)

module Examples.LeftistHeap
  (Val : Set) (_≤_ : Val → Val → Set)
    (≤-refl : ∀ {x} → x ≤ x)
    (≤-trans : ∀ {x y z} → x ≤ y → y ≤ z → x ≤ z)
    (_≤?_ : (x y : Val) → Dec (x ≤ y))
    (≰-invert : ∀ {x y} → ¬ (x ≤ y) → y ≤ x) where

open import Prelude.Function
open import Prelude.InverseImage
open import Refinement
open import Description
open import Ornament hiding ([]; _∷_)
open import Ornament.SequentialComposition
open import Ornament.ParallelComposition
open import Ornament.RefinementSemantics
open import Ornament.ParallelComposition.Swap
open import Examples.Nat
open import Examples.Nat.TotalOrdering renaming (_≤_ to _≤'_; ≤-refl to ≤'-refl; ≤-trans to ≤'-trans; _≤?_ to _≤'?_; ≰-invert to ≰'-invert)
open import Examples.List

open import Function using (id; _∘_)
open import Data.Unit using (⊤; tt)
open import Data.List using ()
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; cong; sym; trans)


--------
-- skeletal binary trees

data TreeTag : Set where
  `nil  : TreeTag
  `node : TreeTag

TreeD : Desc ⊤
TreeD = wrap λ _ → σ TreeTag λ { `nil  → ṿ Data.List.[]
                               ; `node → ṿ (tt Data.List.∷ tt Data.List.∷ Data.List.[]) }

Tree : Set
Tree = μ TreeD tt


--------
-- leftist trees

LTreeOD : OrnDesc Nat ! TreeD
LTreeOD = wrap λ { (ok (con (`nil  ,     _))) → ∇ `nil  (ṿ tt)
                 ; (ok (con (`cons , r , _))) → ∇ `node (Δ[ r' ∈ Nat ] Δ[ _ ∈ r ≤' r' ] ṿ (ok r' , ok r , tt)) }


--------
-- internally labelled trees

ITreeOD : Set → OrnDesc ⊤ ! TreeD
ITreeOD A = wrap λ _ → σ TreeTag λ { `nil  → ṿ tt
                                   ; `node → Δ[ _ ∈ A ] ṿ (ok tt , ok tt , tt) }

ITree : Set → Set
ITree A = μ ⌊ ITreeOD A ⌋ tt

preorder : {A : Set} → ITree A → List A
preorder (con (`nil ,              _)) = []
preorder (con (`node , x , t , u , _)) = x ∷ preorder t ++ preorder u

toList : {A I : Set} {D : Desc I} → Orn ! ⌊ ITreeOD A ⌋ D → {i : I} → μ D i → List A
toList {A} {I} {D} O = Upgrade.u upg preorder (λ _ _ → tt)
  where
    upg : Upgrade (ITree A → List A) ({i : I} → μ D i → List A)
    upg = ∀⁺[[ i ∈ I ]] FRefinement.comp (RSem' O) (ok i) ⇀ toUpgrade Ref-refl


--------
-- heap-ordered trees

HeapOD : OrnDesc Val ! ⌊ ITreeOD Val ⌋
HeapOD = wrap λ { (ok b) → σ TreeTag λ { `nil  → ṿ tt
                                       ; `node → σ[ x ∈ Val ] Δ[ _ ∈ b ≤ x ] ṿ (ok x , ok x , tt) } }

Heap : Val → Set
Heap = μ ⌊ HeapOD ⌋

TreeD-HeapD : Orn ! TreeD ⌊ HeapOD ⌋
TreeD-HeapD = ⌈ ITreeOD Val ⌉ ⊙ ⌈ HeapOD ⌉

Heap' : Val → Tree → Set
Heap' b t = OptP TreeD-HeapD (ok b) t

relax : {b b' : Val} → b' ≤ b → {t : Tree} → Heap' b t → Heap' b' t
relax b'≤b {con (`nil  , _)} p                           = con tt
relax b'≤b {con (`node , _)} (con (x , b≤x , t , u , _)) = con (x , ≤-trans b'≤b b≤x , t , u , tt)


--------
-- leftist heaps

LHeapD : Desc (! ⋈ !)
LHeapD = ⌊ TreeD-HeapD ⊗ ⌈ LTreeOD ⌉ ⌋

LHeap : Val → Nat → Set
LHeap b r = μ LHeapD (ok b , ok r)

lhrelax : {b b' : Val} → b' ≤ b → {r : Nat} → LHeap b r → LHeap b' r
lhrelax = Upgrade.u upg id (λ b'≤b _ → relax b'≤b ** id)
  where ref : (b : Val) (r : Nat) → Refinement Tree (LHeap b r)
        ref b r = FRefinement.comp (toFRefinement (⊗-FSwap TreeD-HeapD ⌈ LTreeOD ⌉ id-FSwap id-FSwap)) (ok (ok b , ok r))
        upg : Upgrade (Tree → Tree) ({b b' : Val} → b' ≤ b → {r : Nat} → LHeap b r → LHeap b' r)
        upg = ∀⁺[[ b ∈ Val ]] ∀⁺[[ b' ∈ Val ]] ∀⁺[ _ ∈ b' ≤ b ] ∀⁺[[ r ∈ Nat ]] ref b r ⇀ toUpgrade (ref b' r)

makeT : (x : Val) {r₀ : Nat} → LHeap x r₀ → {r₁ : Nat} → LHeap x r₁ → Σ[ r ∈ Nat ] LHeap x r
makeT x {r₀} h₀ {r₁} h₁ with r₀ ≤'? r₁
makeT x {r₀} h₀ {r₁} h₁ | yes r₀≤r₁ = suc r₀ , con (x , ≤-refl , r₁ , r₀≤r₁ , h₁ , h₀ , tt)
makeT x {r₀} h₀ {r₁} h₁ | no  r₀≰r₁ = suc r₁ , con (x , ≤-refl , r₀ , ≰'-invert r₀≰r₁ , h₀ , h₁ , tt)

mutual

  merge : {b₀ : Val} {r₀ : Nat} → LHeap b₀ r₀ →
          {b₁ : Val} {r₁ : Nat} → LHeap b₁ r₁ →
          {b : Val} → b ≤ b₀ → b ≤ b₁ → Σ[ r ∈ Nat ] LHeap b r
  merge {b₀} {con (`nil  ,      _)} h₀ h₁ b≤b₀ b≤b₁ = _ , lhrelax b≤b₁ h₁
  merge {b₀} {con (`cons , r₀ , _)} h₀ h₁ b≤b₀ b≤b₁ = merge' h₀ h₁ b≤b₀ b≤b₁

  merge' : {b₀ : Val} {r₀ : Nat} → LHeap b₀ (suc r₀) →
           {b₁ : Val} {r₁ : Nat} → LHeap b₁ r₁ →
           {b : Val} → b ≤ b₀ → b ≤ b₁ → Σ[ r ∈ Nat ] LHeap b r
  merge' h₀ {b₁} {con (`nil , _)} h₁ b≤b₀ b≤b₁ = _ , lhrelax b≤b₀ h₀
  merge' (con (x₀  , b₀≤x₀   , l₀  , r₀≤l₀   , t₀  , u₀  , _))
         {b₁} {con (`cons , r₁ , _)} (con (x₁ , b₁≤x₁ , l₁ , r₁≤l₁ , t₁ , u₁ , _)) b≤b₀ b≤b₁ =
    merge'-with x₀ b₀≤x₀ l₀ r₀≤l₀ t₀ u₀ x₁ b₁≤x₁ l₁ r₁≤l₁ t₁ u₁ b≤b₀ b≤b₁ (x₀ ≤? x₁)

  -- avoiding with-matching to circumvent a possible error of Agda

  merge'-with :
    {b₀ : Val} {r₀ : Nat} → (x₀ : Val) (b₀≤x₀ : b₀ ≤ x₀) (l₀ : Nat) (r₀≤l₀ : r₀ ≤' l₀) (t₀ : LHeap x₀ l₀) (u₀ : LHeap x₀ r₀) →
    {b₁ : Val} {r₁ : Nat} → (x₁ : Val) (b₁≤x₁ : b₁ ≤ x₁) (l₁ : Nat) (r₁≤l₁ : r₁ ≤' l₁) (t₁ : LHeap x₁ l₁) (u₁ : LHeap x₁ r₁) →
    {b : Val} → b ≤ b₀ → b ≤ b₁ → Dec (x₀ ≤ x₁) → Σ[ r ∈ Nat ] LHeap b r
  merge'-with {b₀} {r₀} x₀ b₀≤x₀ l₀ r₀≤l₀ t₀ u₀ {b₁} {r₁} x₁ b₁≤x₁ l₁ r₁≤l₁ t₁ u₁ b≤b₀ b≤b₁ (yes x₀≤x₁) =
    _ , lhrelax (≤-trans b≤b₀ b₀≤x₀)
          (proj₂ (makeT x₀ t₀ (proj₂ (merge u₀ {r₁ = suc r₁} (con (x₁ , x₀≤x₁ , l₁ , r₁≤l₁ , t₁ , u₁ , tt)) ≤-refl ≤-refl))))
  merge'-with {b₀} {r₀} x₀ b₀≤x₀ l₀ r₀≤l₀ t₀ u₀ {b₁} {r₁} x₁ b₁≤x₁ l₁ r₁≤l₁ t₁ u₁ b≤b₀ b≤b₁ (no  x₀≰x₁) =
    _ , lhrelax (≤-trans b≤b₁ b₁≤x₁)
          (proj₂ (makeT x₁ t₁ (proj₂ (merge' {r₀ = r₀} (con (x₀ , ≰-invert x₀≰x₁ , l₀ , r₀≤l₀ , t₀ , u₀ , tt)) u₁ ≤-refl ≤-refl))))

insert : (y : Val) {b : Val} {r : Nat} → LHeap b r → {b' : Val} → b' ≤ b → b' ≤ y → Σ[ r' ∈ Nat ] LHeap b' r'
insert y h = merge h {r₁ = suc zero} (con (y , ≤-refl , zero , ≤'-refl , con tt , con tt , tt))


--------
-- weight-biased leftist trees

WLTreeOD : OrnDesc Nat ! TreeD
WLTreeOD = wrap λ { (ok (con (`nil  ,     _))) → ∇ `nil  (ṿ tt)
                  ; (ok (con (`cons , n , _))) → ∇ `node (Δ[ l ∈ Nat ] Δ[ r ∈ Nat ] Δ[ _ ∈ r ≤' l ] Δ[ _ ∈ n ≡ l + r ] ṿ (ok l , ok r , tt)) }


--------
-- weight-biased leftist heaps

WLHeapD : Desc (! ⋈ !)
WLHeapD = ⌊ TreeD-HeapD ⊗ ⌈ WLTreeOD ⌉ ⌋

WLHeap : Val → Nat → Set
WLHeap b n = μ WLHeapD (ok b , ok n)

wlhrelax : {b b' : Val} → b' ≤ b → {n : Nat} → WLHeap b n → WLHeap b' n
wlhrelax = Upgrade.u upg id λ { b'≤b _ → relax b'≤b ** id }
  where ref : (b : Val) (n : Nat) → Refinement Tree (WLHeap b n)
        ref b r = FRefinement.comp (toFRefinement (⊗-FSwap TreeD-HeapD ⌈ WLTreeOD ⌉ id-FSwap id-FSwap)) (ok (ok b , ok r))
        upg : Upgrade (Tree → Tree) ({b b' : Val} → b' ≤ b → {n : Nat} → WLHeap b n → WLHeap b' n)
        upg = ∀⁺[[ b ∈ Val ]] ∀⁺[[ b' ∈ Val ]] ∀⁺[ _ ∈ b' ≤ b ] ∀⁺[[ n ∈ Nat ]] ref b n ⇀ toUpgrade (ref b' n)


{-# TERMINATING #-}  -- to skip the construction of the well-ordering (_<'_) on natural numbers

mutual

  wmerge : {b₀ : Val} {n₀ : Nat} → WLHeap b₀ n₀ → {b₁ : Val} {n₁ : Nat} → WLHeap b₁ n₁ →
           {b : Val} → b ≤ b₀ → b ≤ b₁ → WLHeap b (n₀ + n₁)
  wmerge {b₀} {con (`nil  ,      _)} h₀ h₁ b≤b₀ b≤b₁ = wlhrelax b≤b₁ h₁
  wmerge {b₀} {con (`cons , n₀ , _)} h₀ h₁ b≤b₀ b≤b₁ = wmerge' h₀ h₁ b≤b₀ b≤b₁

  wmerge' : {b₀ : Val} {n₀ : Nat} → WLHeap b₀ (suc n₀) → {b₁ : Val} {n₁ : Nat} → WLHeap b₁ n₁ →
            {b : Val} → b ≤ b₀ → b ≤ b₁ → WLHeap b (suc n₀ + n₁)
  wmerge' {b₀} {n₀} h₀ {b₁} {con (`nil , _)} h₁ b≤b₀ b≤b₁ = wlhrelax b≤b₀ (subst (WLHeap b₀) (sym (rhs-zero (suc n₀))) h₀)
  wmerge' {b₀} {n₀} (con (x₀ , b₀≤x₀ , l₀ , r₀ , r₀≤l₀ , n₀≡l₀+r₀ , t₀ , u₀ , _))
          {b₁} {con (`cons , n₁ , _)} (con (x₁ , b₁≤x₁ , l₁ , r₁ , r₁≤l₁ , n₁≡l₁+r₁ , t₁ , u₁ , _)) b≤b₀ b≤b₁ =
    wmerge'-with x₀ b₀≤x₀ l₀ r₀ r₀≤l₀ n₀≡l₀+r₀ t₀ u₀ x₁ b₁≤x₁ l₁ r₁ r₁≤l₁ n₁≡l₁+r₁ t₁ u₁ b≤b₀ b≤b₁ (x₀ ≤? x₁)

  wmerge'-with :
    {b₀  : Val} {n₀ : Nat} (x₀ : Val) (b₀≤x₀ : b₀ ≤ x₀) (l₀ r₀ : Nat) (r₀≤l₀ : r₀ ≤' l₀) (n₀≡l₀+r₀ : n₀ ≡ l₀ + r₀)
      (t₀ : WLHeap x₀ l₀) (u₀ : WLHeap x₀ r₀) →
    {b₁  : Val} {n₁ : Nat} (x₁ : Val) (b₁≤x₁ : b₁ ≤ x₁) (l₁ r₁ : Nat) (r₁≤l₁ : r₁ ≤' l₁) (n₁≡l₁+r₁ : n₁ ≡ l₁ + r₁)
      (t₁ : WLHeap x₁ l₁) (u₁ : WLHeap x₁ r₁) →
    {b : Val} → b ≤ b₀ → b ≤ b₁ → Dec (x₀ ≤ x₁) → WLHeap b (suc n₀ + suc n₁)
  wmerge'-with {b₀} {n₀} x₀ b₀≤x₀ l₀ r₀ r₀≤l₀ n₀≡l₀+r₀ t₀ u₀ {b₁} {n₁} x₁ b₁≤x₁ l₁ r₁ r₁≤l₁ n₁≡l₁+r₁ t₁ u₁ b≤b₀ b≤b₁ (yes x₀≤x₁) =
    wlhrelax (≤-trans b≤b₀ b₀≤x₀) 
      (subst (WLHeap x₀) (cong suc (trans (sym (assoc l₀ r₀ (suc n₁))) (cong (λ m → m + suc n₁) (sym n₀≡l₀+r₀))))
        (wmakeT x₀ t₀ (wmerge u₀ {n₁ = suc n₁} (con (x₁ , x₀≤x₁ , l₁ , r₁ , r₁≤l₁ , n₁≡l₁+r₁ , t₁ , u₁ , tt)) ≤-refl ≤-refl)))
  wmerge'-with {b₀} {n₀} x₀ b₀≤x₀ l₀ r₀ r₀≤l₀ n₀≡l₀+r₀ t₀ u₀ {b₁} {n₁} x₁ b₁≤x₁ l₁ r₁ r₁≤l₁ n₁≡l₁+r₁ t₁ u₁ b≤b₀ b≤b₁ (no  x₀≰x₁) =
    wlhrelax (≤-trans b≤b₁ b₁≤x₁)
      (subst (WLHeap x₁) (cong suc (trans (assoc (suc n₀) l₁ r₁)
                                          (trans (sym (rhs-suc n₀ (l₁ + r₁))) (cong (_+_ n₀) (cong suc (sym n₁≡l₁+r₁))))))
        (wmakeT x₁ (wmerge' {n₀ = n₀} (con (x₀ , ≰-invert x₀≰x₁ , l₀ , r₀ , r₀≤l₀ , n₀≡l₀+r₀ , t₀ , u₀ , tt)) t₁ ≤-refl ≤-refl) u₁))

  wmakeT : (x : Val) {n : Nat} (h : WLHeap x n) {n' : Nat} (h' : WLHeap x n') → WLHeap x (suc (n + n'))
  wmakeT x {n} h {n'} h' with n ≤'? n'
  wmakeT x {n} h {n'} h' | yes n≤n' = con (x , ≤-refl , n' , n , n≤n' , comm n n' , h' , h , tt)
  wmakeT x {n} h {n'} h' | no  n≰n' = con (x , ≤-refl , n , n' , ≰'-invert n≰n' , refl , h , h' , tt)
