-- The ordering property and balancing properties of leftist heaps are treated separately when needed.

open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_) renaming (map to _**_)
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
open import Examples.Nat.TotalOrdering renaming (_≤_ to _≤'_; ≤-refl to ≤'-refl; _≤?_ to _≤'?_; ≰-invert to ≰'-invert)
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
                 ; (ok (con (`cons , r , _))) → ∇ `node (Δ[ r' ∶ Nat ] Δ[ _ ∶ r ≤' r' ] ṿ (ok r' , ok r , tt)) }


--------
-- internally labelled trees

ITreeOD : Set → OrnDesc ⊤ ! TreeD
ITreeOD A = wrap λ _ → σ TreeTag λ { `nil  → ṿ tt
                                   ; `node → Δ[ _ ∶ A ] ṿ (ok tt , ok tt , tt) }

ITree : Set → Set
ITree A = μ ⌊ ITreeOD A ⌋ tt

preorder : {A : Set} → ITree A → List A
preorder (con (`nil ,              _)) = []
preorder (con (`node , x , t , u , _)) = x ∷ preorder t ++ preorder u


--------
-- heap-ordered trees

HeapOD : OrnDesc Val ! ⌊ ITreeOD Val ⌋
HeapOD = wrap λ { (ok b) → σ TreeTag λ { `nil  → ṿ tt
                                       ; `node → σ[ x ∶ Val ] Δ[ _ ∶ b ≤ x ] ṿ (ok x , ok x , tt) } }

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

toList : {b : Val} {r : Nat} → LHeap b r → List Val
toList = preorder ∘ forget (⌈ HeapOD ⌉ ⊙ diffOrn-l TreeD-HeapD ⌈ LTreeOD ⌉)

lhrelax : {b b' : Val} → b' ≤ b → {r : Nat} → LHeap b r → LHeap b' r
lhrelax = Upgrade.u upg id λ { b'≤b _ (p , q) → relax b'≤b p , q }
  where ref : (b : Val) (r : Nat) → Refinement Tree (LHeap b r)
        ref b r = FRefinement.comp (toFRefinement (⊗-FSwap TreeD-HeapD ⌈ LTreeOD ⌉ id-FSwap id-FSwap)) (ok (ok b , ok r))
        upg : Upgrade (Tree → Tree) ({b b' : Val} → b' ≤ b → {r : Nat} → LHeap b r → LHeap b' r)
        upg = ∀⁺[[ b ∶ Val ]] ∀⁺[[ b' ∶ Val ]] ∀⁺[ _ ∶ b' ≤ b ] ∀⁺[[ r ∶ Nat ]] ref b r ⇀ toUpgrade (ref b' r)

makeT : (x : Val) {r : Nat} (h : LHeap x r) {r' : Nat} (h' : LHeap x r') → Σ[ r'' ∶ Nat ] LHeap x r''
makeT x {r} h {r'} h' with r ≤'? r'
makeT x {r} h {r'} h' | yes r≤r' = suc r  , con (x , ≤-refl , r' , r≤r' , h' , h , tt)
makeT x {r} h {r'} h' | no  r≰r' = suc r' , con (x , ≤-refl , r , ≰'-invert r≰r' , h , h' , tt)

mutual

  merge : {b : Val} {r : Nat} → LHeap b r → {b' : Val} {r' : Nat} → LHeap b' r' →
          {b'' : Val} → b'' ≤ b → b'' ≤ b' → Σ[ r'' ∶ Nat ] LHeap b'' r''
  merge {b} {con (`nil  ,     _)} h h' b''≤b b''≤b' = _ , lhrelax b''≤b' h'
  merge {b} {con (`cons , r , _)} h h' b''≤b b''≤b' = merge' h h' b''≤b b''≤b'

  merge' : {b : Val} {r : Nat} → LHeap b (suc r) → {b' : Val} {r' : Nat} → LHeap b' r' →
           {b'' : Val} → b'' ≤ b → b'' ≤ b' → Σ[ r'' ∶ Nat ] LHeap b'' r''
  merge' h {b'} {con (`nil , _)} h' b''≤b b''≤b' = _ , lhrelax b''≤b h
  merge' (con (x  , b≤x   , l  , r≤l   , t  , u  , _))
         {b'} {con (`cons , r' , _)} (con (x' , b'≤x' , l' , r'≤l' , t' , u' , _)) b''≤b b''≤b' =
    merge'-with x b≤x l r≤l t u x' b'≤x' l' r'≤l' t' u' b''≤b b''≤b' (x ≤? x')

  -- avoiding with-matching to circumvent a possible error of Agda

  merge'-with :
    {b  : Val} {r  : Nat} → (x  : Val) (b≤x   : b  ≤ x ) (l  : Nat) (r≤l   : r  ≤' l ) (t  : LHeap x  l ) (u  : LHeap x  r ) →
    {b' : Val} {r' : Nat} → (x' : Val) (b'≤x' : b' ≤ x') (l' : Nat) (r'≤l' : r' ≤' l') (t' : LHeap x' l') (u' : LHeap x' r') →
    {b'' : Val} → b'' ≤ b → b'' ≤ b' → Dec (x ≤ x') → Σ[ r'' ∶ Nat ] LHeap b'' r''
  merge'-with {b} {r} x b≤x l r≤l t u {b'} {r'} x' b'≤x' l' r'≤l' t' u' b''≤b b''≤b' (yes x≤x') =
    _ , lhrelax (≤-trans b''≤b b≤x)
          (proj₂ (makeT x t (proj₂ (merge u {r' = suc r'} (con (x' , x≤x' , l' , r'≤l' , t' , u' , tt)) ≤-refl ≤-refl))))
  merge'-with {b} {r} x b≤x l r≤l t u {b'} {r'} x' b'≤x' l' r'≤l' t' u' b''≤b b''≤b' (no  x≰x') =
    _ , lhrelax (≤-trans b''≤b' b'≤x')
          (proj₂ (makeT x' t' (proj₂ (merge' {r = r} (con (x , ≰-invert x≰x' , l , r≤l , t , u , tt)) u' ≤-refl ≤-refl))))

insert : (y : Val) {b : Val} {r : Nat} → LHeap b r → {b' : Val} → b' ≤ b → b' ≤ y → Σ[ r' ∶ Nat ] LHeap b' r'
insert y h = merge h {r' = suc zero} (con (y , ≤-refl , zero , ≤'-refl , con tt , con tt , tt))


--------
-- weight-biased leftist trees

WLTreeOD : OrnDesc Nat ! TreeD
WLTreeOD = wrap λ { (ok (con (`nil  ,     _))) → ∇ `nil  (ṿ tt)
                  ; (ok (con (`cons , n , _))) → ∇ `node (Δ[ l ∶ Nat ] Δ[ r ∶ Nat ] Δ[ _ ∶ r ≤' l ] Δ[ _ ∶ n ≡ l + r ] ṿ (ok l , ok r , tt)) }


--------
-- weight-biased leftist heaps

WLHeapD : Desc (! ⋈ !)
WLHeapD = ⌊ TreeD-HeapD ⊗ ⌈ WLTreeOD ⌉ ⌋

WLHeap : Val → Nat → Set
WLHeap b n = μ WLHeapD (ok b , ok n)

toList-W : {b : Val} {n : Nat} → WLHeap b n → List Val
toList-W = preorder ∘ forget (⌈ HeapOD ⌉ ⊙ diffOrn-l TreeD-HeapD ⌈ WLTreeOD ⌉)

wlhrelax : {b b' : Val} → b' ≤ b → {n : Nat} → WLHeap b n → WLHeap b' n
wlhrelax = Upgrade.u upg id λ { b'≤b _ (p , q) → relax b'≤b p , q }
  where ref : (b : Val) (n : Nat) → Refinement Tree (WLHeap b n)
        ref b r = FRefinement.comp (toFRefinement (⊗-FSwap TreeD-HeapD ⌈ WLTreeOD ⌉ id-FSwap id-FSwap)) (ok (ok b , ok r))
        upg : Upgrade (Tree → Tree) ({b b' : Val} → b' ≤ b → {n : Nat} → WLHeap b n → WLHeap b' n)
        upg = ∀⁺[[ b ∶ Val ]] ∀⁺[[ b' ∶ Val ]] ∀⁺[ _ ∶ b' ≤ b ] ∀⁺[[ n ∶ Nat ]] ref b n ⇀ toUpgrade (ref b' n)


{-# NO_TERMINATION_CHECK #-}  -- to skip the construction of the well-ordering (_<'_) on natural numbers

mutual

  wmerge : {b : Val} {n : Nat} → WLHeap b n → {b' : Val} {n' : Nat} → WLHeap b' n' →
           {b'' : Val} → b'' ≤ b → b'' ≤ b' → WLHeap b'' (n + n')
  wmerge {b} {con (`nil  ,     _)} h h' b''≤b b''≤b' = wlhrelax b''≤b' h'
  wmerge {b} {con (`cons , n , _)} h h' b''≤b b''≤b' = wmerge' h h' b''≤b b''≤b'

  wmerge' : {b : Val} {n : Nat} → WLHeap b (suc n) → {b' : Val} {n' : Nat} → WLHeap b' n' →
            {b'' : Val} → b'' ≤ b → b'' ≤ b' → WLHeap b'' (suc n + n')
  wmerge' {b} {n} h {b'} {con (`nil , _)} h' b''≤b b''≤b' = wlhrelax b''≤b (subst (WLHeap b) (sym (rhs-zero (suc n))) h)
  wmerge' {b} {n} (con (x , b≤x , l , r , r≤l , n≡l+r , t , u , _))
          {b'} {con (`cons , n' , _)} (con (x' , b'≤x' , l' , r' , r'≤l' , n'≡l'+r' , t' , u' , _)) b''≤b b''≤b' =
    wmerge'-with x b≤x l r r≤l n≡l+r t u x' b'≤x' l' r' r'≤l' n'≡l'+r' t' u' b''≤b b''≤b' (x ≤? x')

  wmerge'-with :
    {b  : Val} {n  : Nat} (x  : Val) (b≤x   : b  ≤ x ) (l  r  : Nat) (r≤l   : r  ≤' l ) (n≡l+r    : n  ≡ l  + r ) (t  : WLHeap x  l ) (u  : WLHeap x  r ) →
    {b' : Val} {n' : Nat} (x' : Val) (b'≤x' : b' ≤ x') (l' r' : Nat) (r'≤l' : r' ≤' l') (n'≡l'+r' : n' ≡ l' + r') (t' : WLHeap x' l') (u' : WLHeap x' r') →
    {b'' : Val} → b'' ≤ b → b'' ≤ b' → Dec (x ≤ x') → WLHeap b'' (suc n + suc n')
  wmerge'-with {b} {n} x b≤x l r r≤l n≡l+r t u {b'} {n'} x' b'≤x' l' r' r'≤l' n'≡l'+r' t' u' b''≤b b''≤b' (yes x≤x') =
    wlhrelax (≤-trans b''≤b b≤x) 
      (subst (WLHeap x) (cong suc (trans (sym (assoc l r (suc n'))) (cong (λ m → m + suc n') (sym n≡l+r))))
        (wmakeT x t (wmerge u {n' = suc n'} (con (x' , x≤x' , l' , r' , r'≤l' , n'≡l'+r' , t' , u' , tt)) ≤-refl ≤-refl)))
  wmerge'-with {b} {n} x b≤x l r r≤l n≡l+r t u {b'} {n'} x' b'≤x' l' r' r'≤l' n'≡l'+r' t' u' b''≤b b''≤b' (no  x≰x') =
    wlhrelax (≤-trans b''≤b' b'≤x')
      (subst (WLHeap x') (cong suc (trans (assoc (suc n) l' r')
                                          (trans (sym (rhs-suc n (l' + r'))) (cong (_+_ n) (cong suc (sym n'≡l'+r'))))))
        (wmakeT x' (wmerge' {n = n} (con (x , ≰-invert x≰x' , l , r , r≤l , n≡l+r , t , u , tt)) t' ≤-refl ≤-refl) u'))

  wmakeT : (x : Val) {n : Nat} (t : WLHeap x n) {n' : Nat} (t' : WLHeap x n') → WLHeap x (suc (n + n'))
  wmakeT x {n} t {n'} t' with n ≤'? n'
  wmakeT x {n} t {n'} t' | yes n≤n' = con (x , ≤-refl , n' , n , n≤n' , comm n n' , t' , t , tt)
  wmakeT x {n} t {n'} t' | no  n≰n' = con (x , ≤-refl , n , n' , ≰'-invert n≰n' , refl , t , t' , tt)
