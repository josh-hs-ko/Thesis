-- This module defines pointwise equality of functions, which forms a setoid, and pointwise heterogeneous equality of functions.
-- The category `Fun` of sets and functions is also defined here.
-- The unit type is proved to be terminal in `Fun`.

module Prelude.Function where

open import Prelude.Category

open import Level
open import Function using (_∘_; const; type-signature)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_) renaming (map to _**_)
open import Relation.Binary using (Setoid)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)
open import Relation.Binary.HeterogeneousEquality using (_≅_; ≡-to-≅) renaming (refl to hrefl; cong to hcong; sym to hsym; trans to htrans)


--------
-- pointwise equality of functions

_≐_ : ∀ {a b} {A : Set a} {B : Set b} → (f g : A → B) → Set (a ⊔ b)
f ≐ g = ∀ x → f x ≡ g x

infix 1 _≐_

frefl : ∀ {a b} {A : Set a} {B : Set b} {f : A → B} → f ≐ f
frefl = λ _ → refl

fsym : ∀ {a b} {A : Set a} {B : Set b} {f g : A → B} → f ≐ g → g ≐ f
fsym fgeq = λ x → sym (fgeq x)

ftrans : ∀ {a b} {A : Set a} {B : Set b} {f g h : A → B} → f ≐ g → g ≐ h → f ≐ h
ftrans fgeq gheq = λ x → trans (fgeq x) (gheq x)

FunSetoid : ∀ {a b} → Set a → Set b → Setoid _ _
FunSetoid A B = record { Carrier = A → B; _≈_ = _≐_; isEquivalence = record { refl = frefl; sym = fsym; trans = ftrans } }

fcong-l : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} {f g : A → B} (h : B → C) → f ≐ g → h ∘ f ≐ h ∘ g
fcong-l h feq = λ x → cong h (feq x)

fcong-r : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} {f g : A → B} (h : C → A) → f ≐ g → f ∘ h ≐ g ∘ h
fcong-r h feq = λ x → feq (h x)


--------
-- pointwise heterogeneous equality of functions

_≑_ : ∀ {a b} {A A' : Set a} {B B' : Set b} → (A → B) → (A' → B') → Set a
_≑_ {A = A} {A'} f g = (x : A) (x' : A') → x ≅ x' → f x ≅ g x'

infix 1 _≑_

≑-refl : ∀ {a b} {A : Set a} {B : Set b} {f : A → B} → f ≑ f
≑-refl x .x hrefl = hrefl

≑-sym : ∀ {a b} {A A' : Set a} {B B' : Set b} {f : A → B} {g : A' → B'} → f ≑ g → g ≑ f
≑-sym eq x x' heq = hsym (eq x' x (hsym heq))

≑-trans : ∀ {a b} {A A' A'' : Set a} → A ≡ A' → {B B' B'' : Set b} → {f : A → B} {g : A' → B'} {h : A'' → B''} → f ≑ g → g ≑ h → f ≑ h
≑-trans refl eq eq' x .x hrefl = htrans (eq x x hrefl) (eq' x x hrefl)

≑-cong-l : ∀ {a b c} {A A' : Set a} {B B' : Set b} {C C' : Set c} {f : A → B} {g : A' → B'}
           (h : B → C) (h' : B' → C') → h ≑ h' → f ≑ g → h ∘ f ≑ h' ∘ g
≑-cong-l {f = f} {g} h h' heq fgeq x .x hrefl = heq (f x) (g x) (fgeq x x hrefl)

≑-cong-r : ∀ {a b c} {A A' : Set a} {B B' : Set b} {C C' : Set c} {f : A → B} {g : A' → B'}
           (h : C → A) (h' : C' → A') → h ≑ h' → f ≑ g → f ∘ h ≑ g ∘ h'
≑-cong-r {f = f} {g} h h' heq fgeq x .x hrefl = fgeq (h x) (h' x) (heq x x hrefl)

pointwise : ∀ {a b} {A : Set a} {B B' : Set b} {f : A → B} {g : A → B'} → (∀ x → f x ≅ g x) → f ≑ g
pointwise peq x .x hrefl = peq x

≐-to-≑ : ∀ {a b} {A : Set a} {B : Set b} {f : A → B} {g : A → B} → f ≐ g → f ≑ g
≐-to-≑ feq = pointwise λ x → ≡-to-≅ (feq x)


--------
-- categories of sets and functions

Fun : Category
Fun = record { Object   = Set
             ; Morphism = FunSetoid
             ; _·_ = λ f g → f ∘ g
             ; id  = Function.id
             ; id-l  = λ _ → frefl
             ; id-r  = λ _ → frefl
             ; assoc = λ _ _ _ → frefl
             ; cong-l = fcong-l
             ; cong-r = fcong-r }

! : ∀ {a} {A : Set a} → A → ⊤
! _ = tt

⊤-terminal : Terminal Fun ⊤
⊤-terminal = λ _ → (! , λ _ → frefl)
