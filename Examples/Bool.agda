module Examples.Bool where

open import Prelude.Function
open import Prelude.InverseImage
open import Refinement
open import Description
open import Ornament

open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Product using (Σ; _,_)
open import Data.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)


data BoolTag : Set where
  `false : BoolTag
  `true  : BoolTag

BoolD : Desc ⊤
BoolD = wrap λ _ → σ[ _ ∈ BoolTag ] ṿ []

MaybeOD : Set → OrnDesc ⊤ ! BoolD
MaybeOD A = wrap λ _ → σ BoolTag λ { `false → ṿ tt
                                   ; `true  → Δ[ _ ∈ A ] ṿ tt }

Maybe : Set → Set
Maybe A = μ ⌊ MaybeOD A ⌋ tt

pattern nothing = con (`false ,     _)
pattern just a  = con (`true  , a , _)

mapMaybe : {A B : Set} → (A → B) → Maybe A → Maybe B
mapMaybe f nothing  = nothing
mapMaybe f (just a) = just (f a)

EitherOD : Set → Set → OrnDesc ⊤ ! BoolD
EitherOD A B = wrap λ _ → σ BoolTag λ { `false → Δ[ _ ∈ A ] ṿ tt
                                      ; `true  → Δ[ _ ∈ B ] ṿ tt }

Maybe'OD : {A : Set} (B : A → Set) → OrnDesc (Maybe A) ! ⌊ MaybeOD (Σ A B) ⌋
Maybe'OD B = wrap λ { {._} (ok nothing ) → ∇ `false (ṿ tt)
                    ; {._} (ok (just a)) → ∇ `true  (Δ[ b ∈ B a ] ∇ (a , b) (ṿ tt)) }

Maybe' : {A : Set} → (A → Set) → Maybe A → Set
Maybe' B = μ ⌊ Maybe'OD B ⌋

maybeU : {A B : Set} → Upgrade A B → Upgrade (Maybe A) (Maybe B)
maybeU {A} {B} upg = record
  { P = Maybe' (Upgrade.P upg)
  ; C = λ { nothing  nothing  → ⊤
          ; nothing  (just b) → ⊥
          ; (just a) nothing  → ⊥
          ; (just a) (just b) → Upgrade.C upg a b }
  ; u = λ { nothing  mp            → nothing
          ; (just a) (con (p , _)) → just (Upgrade.u upg a p) }
  ; c = λ { nothing  mp            → tt
          ; (just a) (con (p , _)) → Upgrade.c upg a p } }

maybeFU : {A B : Set} → FUpgrade A B → FUpgrade (Maybe A) (Maybe B)
maybeFU {A} {B} fupg = record
  { P      = Maybe' (FUpgrade.P fupg)
  ; forget = mapMaybe (FUpgrade.forget fupg)
  ; u      = λ { nothing  mp            → nothing
               ; (just a) (con (p , _)) → just (FUpgrade.u fupg a p) }
  ; c      = λ { nothing  mp            → refl
               ; (just a) (con (p , _)) → cong just (FUpgrade.c fupg a p) } }
