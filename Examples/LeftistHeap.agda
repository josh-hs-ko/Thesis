open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_) renaming (map to _**_)
open import Relation.Nullary using (¬_; Dec; yes; no)

module Thesis.Examples.LeftistHeap
  (Val : Set) (_≤_ : Val → Val → Set)
    (≤-refl : ∀ {x} → x ≤ x)
    (≤-trans : ∀ {x y z} → x ≤ y → y ≤ z → x ≤ z)
    (_≤?_ : (x y : Val) → Dec (x ≤ y))
    (≰-invert : ∀ {x y} → ¬ (x ≤ y) → y ≤ x)
  (_⊓_ : Val → Val → Val)
    (⊓-universal-⇒ : ∀ z x y → z ≤ (x ⊓ y) → z ≤ x  ×  z ≤ y)
    (⊓-universal-⇐ : ∀ {z x y} → z ≤ x → z ≤ y → z ≤ (x ⊓ y)) where

open import Thesis.Prelude.Function
open import Thesis.Prelude.InverseImage
open import Thesis.Refinement
open import Thesis.Description
open import Thesis.Ornament
open import Thesis.Ornament.ParallelComposition
open import Thesis.Ornament.RefinementSemantics
open import Thesis.Ornament.ParallelComposition.Swap
open import Thesis.Examples.Nat
open import Thesis.Examples.Nat.TotalOrdering renaming (_≤_ to _≤'_; ≤-refl to ≤'-refl; _≤?_ to _≤'?_; ≰-invert to ≰'-invert)
open import Thesis.Examples.List

open import Function using (id; _∘_)
open import Data.Unit using (⊤; tt)
open import Data.Bool using (Bool; false; true)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; cong; sym; trans)


--------
-- binary trees

TreeD : Desc ⊤
TreeD = wrap λ _ → σ Bool λ { false → ∎
                            ; true  → ṿ tt * ṿ tt }


--------
-- leftist trees

LTreeO : OrnDesc Nat ! TreeD
LTreeO = wrap λ { (ok (con (false , _))) → ∇ false ∎
                ; (ok (con (true  , r))) → ∇ true (Δ[ r' ∶ Nat ] Δ[ _ ∶ r ≤' r' ] ṿ (ok r') * ṿ (ok r)) }


--------
-- internally labelled trees

ITreeO : Set → OrnDesc ⊤ ! TreeD
ITreeO A = wrap λ _ → σ Bool λ { false → ∎
                               ; true  → Δ[ _ ∶ A ] ṿ (ok tt) * ṿ (ok tt) }

ITree : Set → Set
ITree A = μ ⌊ ITreeO A ⌋ tt

preorder : ∀ {A} → ITree A → List A
preorder (con (false , _)) = []
preorder (con (true , x , t , u)) = x ∷ preorder t ++ preorder u


--------
-- min-heaps

HeapO : OrnDesc Val ! TreeD
HeapO = wrap λ { (ok b) → σ Bool λ { false → ∎
                                   ; true  → Δ[ x ∶ Val ] Δ[ _ ∶ b ≤ x ] ṿ (ok x) * ṿ (ok x) } }

ITreeD-HeapD : Orn ! ⌊ ITreeO Val ⌋ ⌊ HeapO ⌋
ITreeD-HeapD =
  wrap λ { (ok b) → σ Bool λ { false → ∎
                             ; true → σ[ x ∶ Val ] Δ[ _ ∶ b ≤ x ] ṿ refl * ṿ refl } }

Heap : Val → Set
Heap = μ ⌊ HeapO ⌋

relax : ∀ {b b'} → b' ≤ b → ∀ {t} → OptP ⌈ HeapO ⌉ (ok b) t → OptP ⌈ HeapO ⌉ (ok b') t
relax b'≤b {con (false , _)} p                       = con tt
relax b'≤b {con (true  , _)} (con (x , b≤x , t , u)) = con (x , ≤-trans b'≤b b≤x , t , u)


--------
-- leftist heaps

LHeapD : Desc (! ⋈ !)
LHeapD = ⌊ ⌈ HeapO ⌉ ⊗ ⌈ LTreeO ⌉ ⌋

LHeap : Val → Nat → Set
LHeap b r = μ LHeapD (ok b , ok r)

toList : ∀ {b r} → LHeap b r → List Val
toList = preorder ∘ forget ITreeD-HeapD ∘ forget (diffOrn-l ⌈ HeapO ⌉ ⌈ LTreeO ⌉)

lhrelax : ∀ {b b'} → b' ≤ b → ∀ {r} → LHeap b r → LHeap b' r
lhrelax = Upgrade.u u id (λ { b'≤b _ (p , q) → relax b'≤b p , q })
  where re = λ b r → FRefinement.comp (toFRefinement (⊗-FSwap ⌈ HeapO ⌉ ⌈ LTreeO ⌉ idFSwap idFSwap)) (ok (ok b , ok r))
        u = ∀⁺[[ b ∶ _ ]] ∀⁺[[ b' ∶ _ ]] ∀⁺[ _ ∶ b' ≤ b ] ∀⁺[[ r ∶ _ ]] re b r ⇀ toUpgrade (re b' r)

makeT : (x : Val) → ∀ {r} (t : LHeap x r) → ∀ {r'} (t' : LHeap x r') → Σ Nat (LHeap x)
makeT x {r} t {r'} t' with r ≤'? r'
makeT x {r} t {r'} t' | yes r≤r' = suc r  , con (x , ≤-refl , r' , r≤r' , t' , t)
makeT x {r} t {r'} t' | no  r≰r' = suc r' , con (x , ≤-refl , r , ≰'-invert r≰r' , t , t')

mutual

  merge : ∀ {b r} → LHeap b r → ∀ {b' r'} → LHeap b' r' → Σ Nat (LHeap (b ⊓ b'))
  merge {b} {con (false , _)} h {b'} h' = _ , lhrelax (proj₂ (⊓-universal-⇒ (b ⊓ b') b b' ≤-refl)) h'
  merge {b} {con (true  , r)} h {b'} h' = merge' h h'

  merge' : ∀ {b r} → LHeap b (suc r) → ∀ {b' r'} → LHeap b' r' → Σ Nat (LHeap (b ⊓ b'))
  merge' {b} {r} h {b'} {con (false , _)} h' =
    _ , lhrelax (proj₁ (⊓-universal-⇒ (b ⊓ b') b b' ≤-refl)) (subst (LHeap b) (sym (rhs-zero (suc r))) h)
  merge' {b} {r} (con (x , b≤x , l , r≤l , t , u)) {b'} {con (true , r')} (con (x' , b'≤x' , l' , r'≤l' , t' , u')) =
    merge'-with x b≤x l r≤l t u x' b'≤x' l' r'≤l' t' u' (x ≤? x')

  -- avoiding with-matching to circumvent a likely bug of Agda

  merge'-with :
    ∀ {b r} → (x : Val) (b≤x : b ≤ x) (l : Nat) (r≤l : r ≤' l) (t : LHeap x l) (u : LHeap x r) →
    ∀ {b' r'} → (x' : Val) (b'≤x' : b' ≤ x') (l' : Nat) (r'≤l' : r' ≤' l') (t' : LHeap x' l') (u' : LHeap x' r') →
    Dec (x ≤ x') → Σ Nat (LHeap (b ⊓ b'))
  merge'-with {b} {r} x b≤x l r≤l t u {b'} {r'} x' b'≤x' l' r'≤l' t' u' (yes x≤x') =
    _ , lhrelax (≤-trans (proj₁ (⊓-universal-⇒ (b ⊓ b') b b' ≤-refl)) b≤x)
          (proj₂ (makeT x t (lhrelax (⊓-universal-⇐ ≤-refl ≤-refl)
            (proj₂ (merge u {r' = suc r'} (con (x' , x≤x' , l' , r'≤l' , t' , u')))))))
  merge'-with {b} {r} x b≤x l r≤l t u {b'} {r'} x' b'≤x' l' r'≤l' t' u' (no  x≰x') =
    _ , lhrelax (≤-trans (proj₂ (⊓-universal-⇒ (b ⊓ b') b b' ≤-refl)) b'≤x')
          (proj₂ (makeT x' t' (lhrelax (⊓-universal-⇐ ≤-refl ≤-refl)
            (proj₂ (merge' {r = r} (con (x , ≰-invert x≰x' , l , r≤l , t , u)) u')))))

insert : (y : Val) → ∀ {b r} → LHeap b r → Σ Nat (LHeap (b ⊓ y))
insert y h = merge h {r' = suc zero} (con (y , ≤-refl , zero , ≤'-refl , con tt , con tt))


--------
-- weight-biased leftist trees

WLTreeO : OrnDesc Nat ! TreeD
WLTreeO = wrap λ { (ok (con (false , _))) → ∇ false ∎
                 ; (ok (con (true ,  n))) → ∇ true (Δ[ l ∶ Nat ] Δ[ r ∶ Nat ] Δ[ _ ∶ r ≤' l ] Δ[ _ ∶ n ≡ l + r ] ṿ (ok l) * ṿ (ok r)) }


--------
-- weight-biased leftist heaps

WLHeapD : Desc (! ⋈ !)
WLHeapD = ⌊ ⌈ HeapO ⌉ ⊗ ⌈ WLTreeO ⌉ ⌋

WLHeap : Val → Nat → Set
WLHeap b n = μ WLHeapD (ok b , ok n)

wlhrelax : ∀ {b b'} → b' ≤ b → ∀ {n} → WLHeap b n → WLHeap b' n
wlhrelax = Upgrade.u u id (λ { b'≤b _ (p , q) → relax b'≤b p , q })
  where re = λ b r → FRefinement.comp (toFRefinement (⊗-FSwap ⌈ HeapO ⌉ ⌈ WLTreeO ⌉ idFSwap idFSwap)) (ok (ok b , ok r))
        u = ∀⁺[[ b ∶ _ ]] ∀⁺[[ b' ∶ _ ]] ∀⁺[ _ ∶ b' ≤ b ] ∀⁺[[ n ∶ _ ]] re b n ⇀ toUpgrade (re b' n)

{-# NO_TERMINATION_CHECK #-}  -- to skip the construction of the well-ordering (_<'_) on natural numbers

mutual

  wmerge : ∀ {b n} → WLHeap b n → ∀ {b' n'} → WLHeap b' n' → WLHeap (b ⊓ b') (n + n')
  wmerge {b} {con (false , _)} h {b'} h' = wlhrelax (proj₂ (⊓-universal-⇒ (b ⊓ b') b b' ≤-refl)) h'
  wmerge {b} {con (true  , n)} h h' = wmerge' h h'

  wmerge' : ∀ {b n} → WLHeap b (suc n) → ∀ {b' n'} → WLHeap b' n' → WLHeap (b ⊓ b') (suc n + n')
  wmerge' {b} {n} h {b'} {con (false , _)} h' =
    wlhrelax (proj₁ (⊓-universal-⇒ (b ⊓ b') b b' ≤-refl)) (subst (WLHeap b) (sym (rhs-zero (suc n))) h)
  wmerge' {b} {n} (con (x , b≤x , l , r , r≤l , n≡l+r , t , u))
          {b'} {con (true , n')} (con (x' , b'≤x' , l' , r' , r'≤l' , n'≡l'+r' , t' , u')) =
    wmerge'-with x b≤x l r r≤l n≡l+r t u x' b'≤x' l' r' r'≤l' n'≡l'+r' t' u' (x ≤? x')

  wmerge'-with :
    ∀ {b n} (x : Val) (b≤x : b ≤ x) (l r : Nat) (r≤l : r ≤' l) (n≡l+r : n ≡ l + r) (t : WLHeap x l) (u : WLHeap x r) →
    ∀ {b' n'} (x' : Val) (b'≤x' : b' ≤ x') (l' r' : Nat) (r'≤l' : r' ≤' l') (n'≡l'+r' : n' ≡ l' + r') (t' : WLHeap x' l') (u' : WLHeap x' r') →
    Dec (x ≤ x') → WLHeap (b ⊓ b') (suc n + suc n')
  wmerge'-with {b} {n} x b≤x l r r≤l n≡l+r t u {b'} {n'} x' b'≤x' l' r' r'≤l' n'≡l'+r' t' u' (yes x≤x') =
    wlhrelax (≤-trans (proj₁ (⊓-universal-⇒ (b ⊓ b') b b' ≤-refl)) b≤x)
      (subst (WLHeap x) (cong suc (trans (sym (assoc l r (suc n'))) (cong (λ m → m + suc n') (sym n≡l+r))))
        (wmakeT x t (wlhrelax (⊓-universal-⇐ {x} ≤-refl ≤-refl)
                              (wmerge u {n' = suc n'} (con (x' , x≤x' , l' , r' , r'≤l' , n'≡l'+r' , t' , u'))))))
  wmerge'-with {b} {n} x b≤x l r r≤l n≡l+r t u {b'} {n'} x' b'≤x' l' r' r'≤l' n'≡l'+r' t' u' (no  x≰x') =
    wlhrelax (≤-trans (proj₂ (⊓-universal-⇒ (b ⊓ b') b b' ≤-refl)) b'≤x')
      (subst (WLHeap x') (cong suc (trans (assoc (suc n) l' r')
                                          (trans (sym (rhs-suc n (l' + r'))) (cong (_+_ n) (cong suc (sym n'≡l'+r'))))))
        (wmakeT x' (wlhrelax (⊓-universal-⇐ {x'} ≤-refl ≤-refl)
                             (wmerge' {n = n} (con (x , ≰-invert x≰x' , l , r , r≤l , n≡l+r , t , u)) t')) u'))

  wmakeT : (x : Val) → ∀ {n} (t : WLHeap x n) → ∀ {n'} (t' : WLHeap x n') → WLHeap x (suc (n + n'))
  wmakeT x {n} t {n'} t' with n ≤'? n'
  wmakeT x {n} t {n'} t' | yes n≤n' = con (x , ≤-refl , n' , n , n≤n' , comm n n' , t' , t)
  wmakeT x {n} t {n'} t' | no  n≰n' = con (x , ≤-refl , n , n' , ≰'-invert n≰n' , refl , t , t')