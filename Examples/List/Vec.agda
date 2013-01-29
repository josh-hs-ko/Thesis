-- Vectors, i.e., length-indexed lists, defined as the optimised predicate for the ornament from natural numbers to lists.

module Thesis.Examples.List.Vec where

open import Thesis.Prelude.Function
open import Thesis.Prelude.InverseImage
open import Thesis.Prelude.Product
open import Thesis.Refinement
open import Thesis.Description
open import Thesis.Ornament
open import Thesis.Ornament.RefinementSemantics
open import Thesis.Examples.Nat
open import Thesis.Examples.List

open import Function using (_∘_)
open import Data.Unit using (⊤; tt)
open import Data.Bool using (Bool; false; true)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; proof-irrelevance)


VecD : (A : Set) → Desc (! ⋈ proj₁)
VecD A = OptPD ⌈ ListOD A ⌉

Vec : Set → Nat → Set
Vec A n = μ (VecD A) (ok tt , ok (tt , n))

VecO : (A : Set) → Orn π₁ ⌊ ListOD A ⌋ (VecD A)
VecO A = OptPO ⌈ ListOD A ⌉

vnil : ∀ {A} → Vec A zero
vnil = con tt

vcons : ∀ {A} → A → ∀ {n} → Vec A n → Vec A (suc n)
vcons x xs = con (x , xs)

Length : Nat → ∀ {A} → List A → Set
Length n {A} xs = OptP (VecO A) (ok (ok tt , ok (tt , n))) xs

LengthFSwap : (A : Set) → FSwap (RSem' (VecO A))
LengthFSwap A =
  wrap λ { {._} (ok (ok _ , ok (_ , n))) →
           record
             { Q = λ { xs → length xs ≡ n }
             ; s = λ { xs →
                       record
                         { to   = to n xs
                         ; from = from n xs
                         ; to-from-inverse = λ _ → proof-irrelevance _ _
                         ; from-to-inverse = λ _ → ULP n xs } } } }
  where to : ∀ n (xs : List A) → Length n xs → length xs ≡ n
        to (con (false , _)) (con (false , _))      l                = refl
        to (con (false , _)) (con (true  , x , xs)) (con (()   , _))
        to (con (true  , n)) (con (false , _))      (con (()   , _))
        to (con (true  , n)) (con (true  , x , xs)) (con (refl , l)) = cong suc (to n xs l)
        from : ∀ n (xs : List A) → length xs ≡ n → Length n xs
        from (con (false , _)) (con (false , _))      eq = con (refl , tt)
        from (con (false , _)) (con (true  , x , xs)) ()
        from (con (true  , n)) (con (false , _))      ()
        from (con (true  , n)) (con (true  , x , xs)) eq = con (refl , from n xs (cong-proj₂ (cong decon eq)))
        ULP : ∀ n (xs : List A) {l l' : Length n xs} → l ≡ l'
        ULP (con (false , _)) (con (false , _))      {con (refl , tt)} {con (refl , tt)} = refl
        ULP (con (false , _)) (con (true  , x , xs)) {con (()   , _ )}
        ULP (con (true  , n)) (con (false , _))      {con (()   , _ )}
        ULP (con (true  , n)) (con (true  , x , xs)) {con (refl , l )} {con (refl , l')} = cong (con ∘ _,_ refl) (ULP n xs)
