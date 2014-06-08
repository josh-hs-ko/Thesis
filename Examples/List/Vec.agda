-- Vectors, i.e., length-indexed lists, defined as the optimised predicate for the ornament from natural numbers to lists.

module Examples.List.Vec where

open import Prelude.Function
open import Prelude.InverseImage
open import Prelude.Product
open import Refinement
open import Description
open import Ornament
open import Ornament.RefinementSemantics
open import Examples.Nat
open import Examples.List

open import Function using (_∘_; flip)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; Σ-syntax; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; proof-irrelevance)


VecD : (A : Set) → Desc (! ⋈ proj₁)
VecD A = OptPD ⌈ ListOD A ⌉

Vec : Set → Nat → Set
Vec A n = μ (VecD A) (ok tt , ok (tt , n))

VecO : (A : Set) → Orn π₁ ⌊ ListOD A ⌋ (VecD A)
VecO A = OptPO ⌈ ListOD A ⌉

vnil : {A : Set} → Vec A zero
vnil = con tt

vcons : {A : Set} → A → {n : Nat} → Vec A n → Vec A (suc n)
vcons x xs = con (x , xs , tt)

Length : Nat → {A : Set} → List A → Set
Length n {A} xs = OptP (VecO A) (ok (ok tt , ok (tt , n))) xs

Length-FSwap : (A : Set) → FSwap (RSem' (VecO A))
Length-FSwap A =
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
        to (con (`nil  ,     _)) (con (`nil  ,          _)) l                    = refl
        to (con (`nil  ,     _)) (con (`cons , x , xs , _)) (con (()   ,     _))
        to (con (`cons , n , _)) (con (`nil  ,          _)) (con (()   ,     _))
        to (con (`cons , n , _)) (con (`cons , x , xs , _)) (con (refl , l , _)) = cong suc (to n xs l)
        from : ∀ n (xs : List A) → length xs ≡ n → Length n xs
        from (con (`nil  ,     _)) (con (`nil  ,          _)) eq = con (refl , tt)
        from (con (`nil  ,     _)) (con (`cons , x , xs , _)) ()
        from (con (`cons , n , _)) (con (`nil  ,          _)) ()
        from (con (`cons , n , _)) (con (`cons , x , xs , _)) eq = con (refl , from n xs (cong proj₁ (cong-proj₂ (cong decon eq))) , tt)
        ULP : ∀ n (xs : List A) {l l' : Length n xs} → l ≡ l'
        ULP (con (`nil  ,     _)) (con (`nil  ,          _)) {con (refl ,     _)} {con (refl ,      _)} = refl
        ULP (con (`nil  ,     _)) (con (`cons , x , xs , _)) {con (()   ,     _)}
        ULP (con (`cons , n , _)) (con (`nil  ,          _)) {con (()   ,     _)}
        ULP (con (`cons , n , _)) (con (`cons , x , xs , _)) {con (refl , l , _)} {con (refl , l' , _)} with ULP n xs {l} {l'}
        ULP (con (`cons , n , _)) (con (`cons , x , xs , _)) {con (refl , l , _)} {con (refl , .l , _)} | refl = refl
