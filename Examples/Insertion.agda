-- The `insert` function used in insertion sort upgraded to work with vectors, sorted lists, and sorted vectors.

open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_) renaming (map to _**_)
open import Relation.Nullary using (¬_; Dec; yes; no)

module Thesis.Examples.Insertion
  (Val : Set) (_≤_ : Val → Val → Set)
    (≤-refl : ∀ {x} → x ≤ x)
    (≤-trans : ∀ {x y z} → x ≤ y → y ≤ z → x ≤ z)
    (_≤?_ : (x y : Val) → Dec (x ≤ y))
    (≰-invert : ∀ {x y} → ¬ (x ≤ y) → y ≤ x)
  (_⊓_ : Val → Val → Val)
    (⊓-universal-⇒ : ∀ z x y → z ≤ (x ⊓ y) → z ≤ x  ×  z ≤ y)
    (⊓-universal-⇐ : ∀ {z x y} → z ≤ x → z ≤ y → z ≤ (x ⊓ y)) where

open import Thesis.Prelude.Function
open import Thesis.Prelude.Product
open import Thesis.Prelude.InverseImage
open import Thesis.Refinement
open import Thesis.Description
open import Thesis.Ornament
open import Thesis.Ornament.ParallelComposition
open import Thesis.Ornament.RefinementSemantics
open import Thesis.Ornament.ParallelComposition.Swap
open import Thesis.Examples.Nat
open import Thesis.Examples.List
open import Thesis.Examples.List.Vec
import Thesis.Examples.List.Sorted as Sorted; open Sorted Val _≤_ ≤-refl ≤-trans

open import Function using (_∘_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Bool using (Bool; false; true)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; _≢_; cong; proof-irrelevance)


--------
-- sorted vectors indexed by lower bound

SVecO : OrnDesc (! ⋈ π₁) pull ⌊ ListO Val ⌋
SVecO = ⌈ SListO ⌉ ⊗ VecO Val

SVec : Val → Nat → Set
SVec b n = μ ⌊ SVecO ⌋ (ok b , ok (ok tt , ok (tt , n)))

svnil : ∀ {b} → SVec b zero
svnil = con tt

svcons : (x : Val) → ∀ {b} → b ≤ x → ∀ {n} → SVec x n → SVec b (suc n)
svcons x le xs = con (x , le , xs)


--------
-- the insertion example

mutual

  insert : Val → List Val → List Val
  insert y (con (false , _)) = y ∷ []
  insert y (con (true  , x , xs)) = insert-with y x xs (y ≤? x)

  -- avoiding with-matching to circumvent a likely bug of Agda

  insert-with : (y x : Val) → List Val → Dec (y ≤ x) → List Val
  insert-with y x xs (yes _) = y ∷ x ∷ xs
  insert-with y x xs (no  _) = x ∷ insert y xs

mutual

  insert-length : ∀ y {n} xs → length xs ≡ n → length (insert y xs) ≡ suc n
  insert-length y (con (false , _))      refl = refl
  insert-length y (con (true  , x , xs)) refl = insert-length-with y x xs refl (y ≤? x)
  
  insert-length-with : ∀ y x {n} xs → length (x ∷ xs) ≡ n → (d : Dec (y ≤ x)) → length (insert-with y x xs d) ≡ suc n
  insert-length-with y x xs refl (yes _) = refl
  insert-length-with y x xs refl (no  _) = cong suc (insert-length y xs refl)

vinsert : Val → ∀ {n} → Vec Val n → Vec Val (suc n)
vinsert = Upgrade.u u insert insert-length
  where r = λ n → FRefinement.comp (toFRefinement (LengthFSwap Val)) (ok (ok tt , ok (tt , n)))
        u = ∀[ _ ∶ Val ] ∀⁺[[ n ∶ Nat ]] r n ⇀ toUpgrade (r (suc n))

mutual

  insert-sorted : ∀ y {b} xs → Sorted b xs → Sorted (b ⊓ y) (insert y xs)
  insert-sorted y {b} (con (false , _)) s = sorted-cons y (proj₂ (⊓-universal-⇒ (b ⊓ y) b y ≤-refl)) sorted-nil
  insert-sorted y {b} (con (true  , x , xs)) (con (b≤x , s)) = insert-sorted-with y x xs b≤x s (y ≤? x)

  insert-sorted-with : ∀ y {b} x xs → b ≤ x → Sorted x xs → (d : Dec (y ≤ x)) → Sorted (b ⊓ y) (insert-with y x xs d)
  insert-sorted-with y {b} x xs b≤x s (yes y≤x) = sorted-cons y (proj₂ (⊓-universal-⇒ (b ⊓ y) b y ≤-refl)) (sorted-cons x y≤x s)
  insert-sorted-with y {b} x xs b≤x s (no  y≰x) = sorted-cons x (≤-trans (proj₁ (⊓-universal-⇒ (b ⊓ y) b y ≤-refl)) b≤x)
                                                                (sorted-relax (⊓-universal-⇐ ≤-refl (≰-invert y≰x)) (insert-sorted y xs s))

sinsert : (y : Val) → ∀ {b} → SList b → SList (b ⊓ y)
sinsert = Upgrade.u u insert insert-sorted
  where r = λ b → FRefinement.comp (RSem' ⌈ SListO ⌉) (ok b)
        u = ∀[ y ∶ Val ] ∀⁺[[ b ∶ _ ]] r b ⇀ toUpgrade (r (b ⊓ y))

svinsert : (y : Val) → ∀ {b n} → SVec b n → SVec (b ⊓ y) (suc n)
svinsert = Upgrade.u u insert (λ y xs → insert-sorted y xs ** insert-length y xs)
  where r = λ b n → FRefinement.comp (toFRefinement (⊗-FSwap ⌈ SListO ⌉ (VecO Val) idFSwap (LengthFSwap Val))) (ok (ok b , ok (ok tt , ok (tt , n))))
        u = ∀[ y ∶ Val ] ∀⁺[[ b ∶ _ ]] ∀⁺[[ n ∶ _ ]] r b n ⇀ toUpgrade (r (b ⊓ y) (suc n))