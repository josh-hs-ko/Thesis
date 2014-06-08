-- The `insert` function used in insertion sort upgraded to work with vectors, ordered lists, and ordered vectors.

open import Data.Product using (Σ; Σ-syntax; _,_; proj₁; proj₂; _×_) renaming (map to _**_)
open import Relation.Nullary using (¬_; Dec; yes; no)

module Examples.Insertion
  (Val : Set) (_≤_ : Val → Val → Set)
    (≤-refl : ∀ {x} → x ≤ x)
    (≤-trans : ∀ {x y z} → x ≤ y → y ≤ z → x ≤ z)
    (_≤?_ : (x y : Val) → Dec (x ≤ y))
    (≰-invert : ∀ {x y} → ¬ (x ≤ y) → y ≤ x) where

open import Prelude.Function
open import Prelude.Product
open import Prelude.InverseImage
open import Refinement
open import Description
open import Ornament hiding ([]; _∷_)
open import Ornament.ParallelComposition
open import Ornament.RefinementSemantics
open import Ornament.ParallelComposition.Swap
open import Examples.Nat
open import Examples.List
open import Examples.List.Vec
import Examples.List.Ordered as Ordered; open Ordered Val _≤_

open import Function using (_∘_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; _≢_; cong; proof-irrelevance)


--------
-- ordered vectors indexed by lower bound

OrdVecOD : OrnDesc (! ⋈ π₁) pull ⌊ ListOD Val ⌋
OrdVecOD = ⌈ OrdListOD ⌉ ⊗ VecO Val

OrdVec : Val → Nat → Set
OrdVec b n = μ ⌊ OrdVecOD ⌋ (ok b , ok (ok tt , ok (tt , n)))

ovnil : {b : Val} → OrdVec b zero
ovnil = con tt

ovcons : (x : Val) {b : Val} → b ≤ x → {n : Nat} → OrdVec x n → OrdVec b (suc n)
ovcons x le xs = con (x , le , xs , tt)


--------
-- the insertion example

mutual

  insert : Val → List Val → List Val
  insert y (con (`nil  ,          _)) = y ∷ []
  insert y (con (`cons , x , xs , _)) = insert-with y x xs (y ≤? x)

  -- avoiding with-matching to circumvent a possible error of Agda

  insert-with : (y x : Val) → List Val → Dec (y ≤ x) → List Val
  insert-with y x xs (yes _) = y ∷ x ∷ xs
  insert-with y x xs (no  _) = x ∷ insert y xs

mutual

  insert-length : (y : Val) {n : Nat} (xs : List Val) → length xs ≡ n → length (insert y xs) ≡ suc n
  insert-length y (con (`nil  ,          _)) refl = refl
  insert-length y (con (`cons , x , xs , _)) refl = insert-length-with y x xs refl (y ≤? x)
  
  insert-length-with : (y x : Val) {n : Nat} (xs : List Val) → length (x ∷ xs) ≡ n → (d : Dec (y ≤ x)) → length (insert-with y x xs d) ≡ suc n
  insert-length-with y x xs refl (yes _) = refl
  insert-length-with y x xs refl (no  _) = cong suc (insert-length y xs refl)

vinsert : Val → {n : Nat} → Vec Val n → Vec Val (suc n)
vinsert = Upgrade.u upg insert insert-length
  where ref : (n : Nat) → Refinement (List Val) (Vec Val n)
        ref n = FRefinement.comp (toFRefinement (Length-FSwap Val)) (ok (ok tt , ok (tt , n)))
        upg : Upgrade (Val → List Val → List Val) (Val → {n : Nat} → Vec Val n → Vec Val (suc n))
        upg = ∀[ _ ∈ Val ] ∀⁺[[ n ∈ Nat ]] ref n ⇀ toUpgrade (ref (suc n))

mutual

  insert-ordered : (y : Val) {b : Val} (xs : List Val) → Ordered b xs →
                   {b' : Val} → b' ≤ b → b' ≤ y → Ordered b' (insert y xs)
  insert-ordered y {b} (con (`nil  ,          _)) s                   b'≤b b'≤y = ordered-cons y b'≤y ordered-nil
  insert-ordered y {b} (con (`cons , x , xs , _)) (con (b≤x , s , _)) b'≤b b'≤y = insert-ordered-with y x xs b≤x s (y ≤? x) b'≤b b'≤y

  insert-ordered-with : (y : Val) {b : Val} (x : Val) (xs : List Val) → b ≤ x → Ordered x xs → (d : Dec (y ≤ x)) →
                        {b' : Val} → b' ≤ b → b' ≤ y → Ordered b' (insert-with y x xs d)
  insert-ordered-with y {b} x xs b≤x s (yes y≤x) b'≤b b'≤y = ordered-cons y b'≤y (ordered-cons x y≤x s)
  insert-ordered-with y {b} x xs b≤x s (no  y≰x) b'≤b b'≤y = ordered-cons x (≤-trans b'≤b b≤x) (insert-ordered y xs s ≤-refl (≰-invert y≰x))

oinsert : (y : Val) {b : Val} → OrdList b → {b' : Val} → b' ≤ b → b' ≤ y → OrdList b'
oinsert = Upgrade.u upg insert insert-ordered
  where ref : (b : Val) → Refinement (List Val) (OrdList b)
        ref b = FRefinement.comp (RSem' ⌈ OrdListOD ⌉) (ok b)
        upg : Upgrade (Val → List Val → List Val) ((y : Val) {b : Val} → OrdList b → {b' : Val} → b' ≤ b → b' ≤ y → OrdList b')
        upg = ∀[ y ∈ Val ] ∀⁺[[ b ∈ Val ]] ref b ⇀ (∀⁺[[ b' ∈ Val ]] ∀⁺[ _ ∈ b' ≤ b ] ∀⁺[ _ ∈ b' ≤ y ] toUpgrade (ref b'))

ovinsert : (y : Val) {b : Val} {n : Nat} → OrdVec b n → {b' : Val} → b' ≤ b → b' ≤ y → OrdVec b' (suc n)
ovinsert = Upgrade.u upg insert
             λ { y xs (ordered-xs , length-xs) b'≤b b'≤y → insert-ordered y xs ordered-xs b'≤b b'≤y , insert-length y xs length-xs }
  where
    ref : (b : Val) (n : Nat) → Refinement (List Val) (OrdVec b n)
    ref b n = FRefinement.comp (toFRefinement (⊗-FSwap ⌈ OrdListOD ⌉ (VecO Val) id-FSwap (Length-FSwap Val))) (ok (ok b , ok (ok tt , ok (tt , n))))
    upg : Upgrade (Val → List Val → List Val)
                  ((y : Val) {b : Val} {n : Nat} → OrdVec b n → {b' : Val} → b' ≤ b → b' ≤ y → OrdVec b' (suc n))
    upg = ∀[ y ∈ Val ] ∀⁺[[ b ∈ Val ]] ∀⁺[[ n ∈ Nat ]] ref b n ⇀ (∀⁺[[ b' ∈ Val ]] ∀⁺[ _ ∈ b' ≤ b ] ∀⁺[ _ ∈ b' ≤ y ] toUpgrade (ref b' (suc n)))
