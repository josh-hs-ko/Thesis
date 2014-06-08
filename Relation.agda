-- Basic definitions of subsets and relations, combinators for specifying nondeterministic computation,
-- relational inclusion wrapped up as preorder and setoid, combinators for reasoning with relations,
-- componentwise relations between families of sets, and definition and properties of relators.

module Relation where

open import Prelude.Category.Isomorphism
open import Prelude.Function
open import Prelude.Function.Fam
open import Prelude.Preorder
open import Description

open import Function using (id; _∘_; flip)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; Σ-syntax; _,_; proj₁; proj₂; _×_)
open import Data.List using (List; []; _∷_)
open import Relation.Binary using (Setoid; Preorder)
import Relation.Binary.PreorderReasoning as PreorderReasoning
import Relation.Binary.EqReasoning as EqReasoning
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym; trans) renaming (setoid to ≡-Setoid)


--------
-- subsets

℘ : Set → Set₁
℘ A = A → Set

_⊑_ : {A : Set} → ℘ A → ℘ A → Set
s ⊑ t = ∀ x → s x → t x

return : {A : Set} → A → ℘ A
return = _≡_

_>>=_ : {A B : Set} → (S : ℘ A) → (A → ℘ B) → ℘ B
_>>=_ {A} s f = λ y → Σ[ x ∈ A ] s x × f x y

map℘ : {A B : Set} → (A → B) → ℘ A → ℘ B
map℘ f s = s >>= (return ∘ f)

map℘-monotonic : {A B : Set} (f : A → B) {s t : ℘ A} → s ⊑ t → map℘ f s ⊑ map℘ f t
map℘-monotonic f s⊑t y (x , sx , eq) = x , s⊑t x sx , eq

map℘₂ : {A B C : Set} → (A → B → C) → ℘ A → ℘ B → ℘ C
map℘₂ f s t = s >>= λ x → t >>= λ y → return (f x y)

map℘₂-monotonic : {A B C : Set} (f : A → B → C) {s t : ℘ A} {u v : ℘ B} → s ⊑ t → u ⊑ v → map℘₂ f s u ⊑ map℘₂ f t v
map℘₂-monotonic f s⊑t u⊑v z (x , sx , y , uy , eq) = x , s⊑t x sx , y , u⊑v y uy , eq

any : {A : Set} → ℘ A
any _ = ⊤

any>>=_ : {A B : Set} → (A → ℘ B) → ℘ B
any>>=_ {A} f = λ y → Σ[ x ∈ A ] f x y

infix 2 any>>=_

none : {A : Set} → ℘ A
none _ = ⊥


--------
-- relations

_↝⁻_ : Set → Set → Set₁
X ↝⁻ Y = X → ℘ Y

fun⁻ : {X Y : Set} → (X → Y) → X ↝⁻ Y
fun⁻ f = return ∘ f

idR⁻ : {X : Set} → X ↝⁻ X
idR⁻ = fun⁻ id

infix 6 _º⁻

_º⁻ : {X Y : Set} → (X ↝⁻ Y) → Y ↝⁻ X
R º⁻ = flip R

infixr 4 _•⁻_

_•⁻_ : {X Y Z : Set} → (Y ↝⁻ Z) → (X ↝⁻ Y) → X ↝⁻ Z
R •⁻ S = λ x → S x >>= R


--------
-- relational inclusion

infix 3 _⊆⁻_

record _⊆⁻_ {X Y : Set} (R S : X ↝⁻ Y) : Set where
  constructor wrap
  field
    comp : ∀ x → R x ⊑ S x

modus-ponens-⊆⁻ : {X Y : Set} {R S : X ↝⁻ Y} → R ⊆⁻ S → (x : X) (y : Y) → R x y → S x y
modus-ponens-⊆⁻ = _⊆⁻_.comp

infix 3 _⊇⁻_

_⊇⁻_ : {X Y : Set} → (X ↝⁻ Y) → (X ↝⁻ Y) → Set
R ⊇⁻ S = S ⊆⁻ R

⊆⁻-refl : {X Y : Set} {R : X ↝⁻ Y} → R ⊆⁻ R
⊆⁻-refl = wrap λ _ _ → id

⊆⁻-trans : {X Y : Set} {R S T : X ↝⁻ Y} → R ⊆⁻ S → S ⊆⁻ T → R ⊆⁻ T
⊆⁻-trans (wrap R⊆⁻S) (wrap S⊆⁻T) = wrap λ x y → S⊆⁻T x y ∘ R⊆⁻S x y

⊆⁻-Preorder : (X Y : Set) → Preorder _ _ _
⊆⁻-Preorder X Y =
  record { Carrier = X ↝⁻ Y
         ; _≈_ = _≡_
         ; _∼_ = _⊆⁻_
         ; isPreorder =
             record { isEquivalence = Setoid.isEquivalence (≡-Setoid _)
                    ; reflexive     = λ { {._} refl → ⊆⁻-refl }
                    ; trans         = ⊆⁻-trans } }

⊇⁻-Preorder : (X Y : Set) → Preorder _ _ _
⊇⁻-Preorder X Y = ConversePreorder (⊆⁻-Preorder X Y)

º⁻-monotonic : {X Y : Set} {R S : X ↝⁻ Y} → R ⊆⁻ S → R º⁻ ⊆⁻ S º⁻
º⁻-monotonic (wrap R⊆⁻S) = wrap λ y x r → R⊆⁻S x y r

•⁻-monotonic : {X Y Z : Set} {R S : Y ↝⁻ Z} {T U : X ↝⁻ Y} → R ⊆⁻ S → T ⊆⁻ U → R •⁻ T ⊆⁻ S •⁻ U
•⁻-monotonic (wrap R⊆⁻S) (wrap T⊆⁻U) = wrap λ { x z (y , t , r) → y , T⊆⁻U x y t , R⊆⁻S y z r }

•⁻-monotonic-l : {X Y Z : Set} {R S : X ↝⁻ Y} (T : Y ↝⁻ Z) → R ⊆⁻ S → T •⁻ R ⊆⁻ T •⁻ S
•⁻-monotonic-l T = •⁻-monotonic ⊆⁻-refl

•⁻-monotonic-r : {X Y Z : Set} {R S : X ↝⁻ Y} (T : Z ↝⁻ X) → R ⊆⁻ S → R •⁻ T ⊆⁻ S •⁻ T
•⁻-monotonic-r T = flip •⁻-monotonic ⊆⁻-refl


--------
-- relational bi-inclusion

≃⁻-Setoid : (X Y : Set) → Setoid _ _
≃⁻-Setoid X Y = PreorderSetoid (⊆⁻-Preorder X Y)

infix 3 _≃⁻_

_≃⁻_ : {X Y : Set} → (X ↝⁻ Y) → (X ↝⁻ Y) → Set
_≃⁻_ {X} {Y} = Setoid._≈_ (≃⁻-Setoid X Y)

≃⁻-refl : {X Y : Set} {R : X ↝⁻ Y} → R ≃⁻ R
≃⁻-refl {X} {Y} = Setoid.refl (≃⁻-Setoid X Y)

≃⁻-sym : {X Y : Set} {R S : X ↝⁻ Y} → R ≃⁻ S → S ≃⁻ R
≃⁻-sym {X} {Y} = Setoid.sym (≃⁻-Setoid X Y)

≃⁻-trans : {X Y : Set} {R S T : X ↝⁻ Y} → R ≃⁻ S → S ≃⁻ T → R ≃⁻ T
≃⁻-trans {X} {Y} = Setoid.trans (≃⁻-Setoid X Y)

fun⁻-preserves-comp : {X Y Z : Set} (f : Y → Z) (g : X → Y) → fun⁻ (f ∘ g) ≃⁻ fun⁻ f •⁻ fun⁻ g
fun⁻-preserves-comp f g = wrap (λ { x ._ refl → g x , refl , refl }) , wrap (λ { x ._ (._ , refl , refl) → refl })

º⁻-preserves-idR⁻ : {X : Set} → idR⁻ º⁻ ≃⁻ idR⁻ {X}
º⁻-preserves-idR⁻ = wrap (λ { x ._ refl → refl }) , wrap (λ { x ._ refl → refl })

º⁻-preserves-comp : {X Y Z : Set} (R : Y ↝⁻ Z) (S : X ↝⁻ Y) → (R •⁻ S) º⁻ ≃⁻ S º⁻ •⁻ R º⁻
º⁻-preserves-comp R S = wrap (λ { z x (y , s , r) → y , r , s }) , wrap (λ { z x (y , r , s) → y , s , r })

fun⁻-cong : {X Y : Set} {f g : X → Y} → f ≐ g → fun⁻ f ≃⁻ fun⁻ g
fun⁻-cong f≐g = wrap (λ { x ._ refl → fsym f≐g x }) , wrap (λ { x ._ refl → f≐g x })

fun⁻-simple : {X Y : Set} (f : X → Y) → fun⁻ f •⁻ fun⁻ f º⁻ ⊆⁻ idR⁻
fun⁻-simple f = wrap λ { ._ ._ (x , refl , refl) → refl }

fun⁻-entire : {X Y : Set} (f : X → Y) → idR⁻ ⊆⁻ fun⁻ f º⁻ •⁻ fun⁻ f
fun⁻-entire f = wrap λ { x .x refl → f x , refl , refl }

º⁻-cong : {X Y : Set} {R S : X ↝⁻ Y} → R ≃⁻ S → R º⁻ ≃⁻ S º⁻
º⁻-cong (R⊆⁻S , R⊇⁻S) = º⁻-monotonic R⊆⁻S , º⁻-monotonic R⊇⁻S

idR⁻-l : {X Y : Set} (R : X ↝⁻ Y) → idR⁻ •⁻ R ≃⁻ R
idR⁻-l R = (wrap λ { x y (.y , r , refl) → r }) , wrap (λ x y r → y , r , refl)

idR⁻-r : {X Y : Set} (R : X ↝⁻ Y) → R •⁻ idR⁻ ≃⁻ R
idR⁻-r R = (wrap λ { x y (.x , refl , r) → r }) , wrap (λ x y r → x , refl , r)

•⁻-cong : {X Y Z : Set} {R S : Y ↝⁻ Z} {T U : X ↝⁻ Y} → R ≃⁻ S → T ≃⁻ U → R •⁻ T ≃⁻ S •⁻ U
•⁻-cong (R⊆⁻S , R⊇⁻S) (T⊆⁻U , T⊇⁻U) = •⁻-monotonic R⊆⁻S T⊆⁻U , •⁻-monotonic R⊇⁻S T⊇⁻U

•⁻-cong-l : {X Y Z : Set} {R S : X ↝⁻ Y} (T : Y ↝⁻ Z) → R ≃⁻ S → T •⁻ R ≃⁻ T •⁻ S
•⁻-cong-l T = •⁻-cong ≃⁻-refl

•⁻-cong-r : {X Y Z : Set} {R S : X ↝⁻ Y} (T : Z ↝⁻ X) → R ≃⁻ S → R •⁻ T ≃⁻ S •⁻ T
•⁻-cong-r T = flip •⁻-cong ≃⁻-refl

•⁻-assoc : {X Y Z W : Set} (R : Z ↝⁻ W) (S : Y ↝⁻ Z) (T : X ↝⁻ Y) → (R •⁻ S) •⁻ T ≃⁻ R •⁻ (S •⁻ T)
•⁻-assoc R S T = wrap (λ { x w (y , t , z , s , r) → z , (y , t , s) , r }) , wrap (λ { x w (z , (y , t , s) , r) → y , t , z , s , r })

iso⁻-conv : {X Y : Set} → (iso : Iso Fun X Y) → fun⁻ (Iso.to iso) º⁻ ≃⁻ fun⁻ (Iso.from iso)
iso⁻-conv iso =
  (wrap (λ y x eq → trans (sym (cong (from iso) eq)) (from-to-inverse iso x))) ,
  (wrap (λ y x eq → trans (sym (cong (to   iso) eq)) (to-from-inverse iso y)))
  where open Iso Fun

iso⁻-idR⁻ : {X Y : Set} → (iso : Iso Fun X Y) →
            fun⁻ (Iso.to iso) •⁻ fun⁻ (Iso.to iso) º⁻ ≃⁻ idR⁻
iso⁻-idR⁻ {Y = Y} iso =
  begin
    fun⁻ (Iso.to iso) •⁻ fun⁻ (Iso.to iso) º⁻
      ≃⁻⟨ •⁻-cong-l (fun⁻ (Iso.to iso)) (iso⁻-conv iso) ⟩
    fun⁻ (Iso.to iso) •⁻ fun⁻ (Iso.from iso)
      ≃⁻⟨ Setoid.sym setoid (fun⁻-preserves-comp (Iso.to iso) (Iso.from iso)) ⟩
    fun⁻ (Iso.to iso ∘ Iso.from iso)
      ≃⁻⟨ fun⁻-cong (Iso.to-from-inverse iso) ⟩
    idR⁻
  □
  where setoid = ≃⁻-Setoid Y Y
        open EqReasoning setoid renaming (_≈⟨_⟩_ to _≃⁻⟨_⟩_; _∎ to _□)

fun⁻-shunting-l-⇒ : {X Y Z : Set} (f : Y → Z) (R : X ↝⁻ Y) (S : X ↝⁻ Z) → fun⁻ f •⁻ R ⊆⁻ S → R ⊆⁻ fun⁻ f º⁻ •⁻ S
fun⁻-shunting-l-⇒ f R S  =
  begin
    fun⁻ f •⁻ R ⊆⁻ S
      ⇒⟨ •⁻-monotonic-l (fun⁻ f º⁻) ⟩
    fun⁻ f º⁻ •⁻ fun⁻ f •⁻ R ⊆⁻ fun⁻ f º⁻ •⁻ S
      ⇒⟨ ⊆⁻-trans (proj₁ (•⁻-assoc (fun⁻ f º⁻) (fun⁻ f) R)) ⟩
    (fun⁻ f º⁻ •⁻ fun⁻ f) •⁻ R ⊆⁻ fun⁻ f º⁻ •⁻ S
      ⇒⟨ ⊆⁻-trans (•⁻-monotonic-r R (fun⁻-entire f)) ⟩
    idR⁻ •⁻ R ⊆⁻ fun⁻ f º⁻ •⁻ S
      ⇒⟨ ⊆⁻-trans (proj₂ (idR⁻-l R)) ⟩
    R ⊆⁻ fun⁻ f º⁻ •⁻ S
  □
  where open PreorderReasoning ⇒-Preorder renaming (_∼⟨_⟩_ to _⇒⟨_⟩_; _∎ to _□)

fun⁻-shunting-l-⇐ : {X Y Z : Set} (f : Y → Z) (R : X ↝⁻ Y) (S : X ↝⁻ Z) → R ⊆⁻ fun⁻ f º⁻ •⁻ S → fun⁻ f •⁻ R ⊆⁻ S
fun⁻-shunting-l-⇐ f R S  =
  begin
    R ⊆⁻ fun⁻ f º⁻ •⁻ S
      ⇒⟨ •⁻-monotonic-l (fun⁻ f) ⟩
    fun⁻ f •⁻ R ⊆⁻ fun⁻ f •⁻ fun⁻ f º⁻ •⁻ S
      ⇒⟨ flip ⊆⁻-trans (proj₂ (•⁻-assoc (fun⁻ f) (fun⁻ f º⁻) S)) ⟩
    fun⁻ f •⁻ R ⊆⁻ (fun⁻ f •⁻ fun⁻ f º⁻) •⁻ S
      ⇒⟨ flip ⊆⁻-trans (•⁻-monotonic-r S (fun⁻-simple f)) ⟩
    fun⁻ f •⁻ R ⊆⁻ idR⁻ •⁻ S
      ⇒⟨ flip ⊆⁻-trans (proj₁ (idR⁻-l S)) ⟩
    fun⁻ f •⁻ R ⊆⁻ S
  □
  where open PreorderReasoning ⇒-Preorder renaming (_∼⟨_⟩_ to _⇒⟨_⟩_; _∎ to _□)

fun⁻-shunting-r-⇒ : {X Y Z : Set} (f : Y → X) (R : Y ↝⁻ Z) (S : X ↝⁻ Z) → R •⁻ fun⁻ f º⁻ ⊆⁻ S → R ⊆⁻ S •⁻ fun⁻ f
fun⁻-shunting-r-⇒ f R S =
  begin
    R •⁻ fun⁻ f º⁻ ⊆⁻ S
      ⇒⟨ º⁻-monotonic ⟩
    (R •⁻ fun⁻ f º⁻) º⁻ ⊆⁻ S º⁻
      ⇒⟨ ⊆⁻-trans (proj₂ (º⁻-preserves-comp R (fun⁻ f º⁻))) ⟩
    fun⁻ f •⁻ R º⁻ ⊆⁻ S º⁻
      ⇒⟨ fun⁻-shunting-l-⇒ f (R º⁻) (S º⁻) ⟩
    R º⁻ ⊆⁻ fun⁻ f º⁻ •⁻ S º⁻
      ⇒⟨ flip ⊆⁻-trans (proj₂ (º⁻-preserves-comp S (fun⁻ f))) ⟩
    R º⁻ ⊆⁻ (S •⁻ fun⁻ f) º⁻
      ⇒⟨ º⁻-monotonic ⟩
    R ⊆⁻ S •⁻ fun⁻ f
  □
  where open PreorderReasoning ⇒-Preorder renaming (_∼⟨_⟩_ to _⇒⟨_⟩_; _∎ to _□)

fun⁻-shunting-r-⇐ : {X Y Z : Set} (f : Y → X) (R : Y ↝⁻ Z) (S : X ↝⁻ Z) → R ⊆⁻ S •⁻ fun⁻ f → R •⁻ fun⁻ f º⁻ ⊆⁻ S
fun⁻-shunting-r-⇐ f R S =
  begin
    R •⁻ fun⁻ f º⁻ ⊆⁻ S
      ⇐⟨ º⁻-monotonic ⟩
    (R •⁻ fun⁻ f º⁻) º⁻ ⊆⁻ S º⁻
      ⇐⟨ ⊆⁻-trans (proj₁ (º⁻-preserves-comp R (fun⁻ f º⁻))) ⟩
    fun⁻ f •⁻ R º⁻ ⊆⁻ S º⁻
      ⇐⟨ fun⁻-shunting-l-⇐ f (R º⁻) (S º⁻) ⟩
    R º⁻ ⊆⁻ fun⁻ f º⁻ •⁻ S º⁻
      ⇐⟨ flip ⊆⁻-trans (proj₁ (º⁻-preserves-comp S (fun⁻ f))) ⟩
    R º⁻ ⊆⁻ (S •⁻ fun⁻ f) º⁻
      ⇐⟨ º⁻-monotonic ⟩
    R ⊆⁻ S •⁻ fun⁻ f
  □
  where open PreorderReasoning ⇐-Preorder renaming (_∼⟨_⟩_ to _⇐⟨_⟩_; _∎ to _□)


--------
-- componentwise relations between families of sets

record _↝_ {I : Set} (X Y : I → Set) : Set₁ where
  constructor wrap
  field
    comp : ∀ i → X i ↝⁻ Y i

_!! : {I : Set} {X Y : I → Set} → (X ↝ Y) → ∀ i → X i ↝⁻ Y i
_!! = _↝_.comp

fun : {I : Set} {X Y : I → Set} → (X ⇉ Y) → X ↝ Y
fun f = wrap λ i → fun⁻ (f {i})

idR : {I : Set} {X : I → Set} → X ↝ X
idR = fun id

α : {I : Set} {D : Desc I} → Ḟ D (μ D) ↝ μ D
α = fun con

infix 6 _º

_º : {I : Set} {X Y : I → Set} → X ↝ Y → Y ↝ X
(R º) = wrap λ i → ((R !!) i º⁻)

infixr 4 _•_

_•_ : {I : Set} {X Y Z : I → Set} → Y ↝ Z → X ↝ Y → X ↝ Z
(R • S) = wrap λ i → (R !!) i •⁻ (S !!) i

infix 3 _⊆_

record _⊆_ {I : Set} {X Y : I → Set} (R S : X ↝ Y) : Set where
  constructor wrap
  field
    comp : ∀ i → (R !!) i ⊆⁻ (S !!) i

modus-ponens-⊆ : {I : Set} {X Y : I → Set} {R S : X ↝ Y} → R ⊆ S → ∀ i (x : X i) (y : Y i) → (R !!) i x y → (S !!) i x y
modus-ponens-⊆ (wrap R⊆S) i x y r = modus-ponens-⊆⁻ (R⊆S i) x y r

⊆-refl : {I : Set} {X Y : I → Set} {R : X ↝ Y} → R ⊆ R
⊆-refl = wrap λ i → ⊆⁻-refl

⊆-trans : {I : Set} {X Y : I → Set} {R S T : X ↝ Y} → R ⊆ S → S ⊆ T → R ⊆ T
⊆-trans (wrap R⊆S) (wrap S⊆T) = wrap λ i → ⊆⁻-trans (R⊆S i) (S⊆T i)

⊆-Preorder : {I : Set} (X Y : I → Set) → Preorder _ _ _
⊆-Preorder X Y =
  record { Carrier = X ↝ Y
         ; _≈_ = _≡_
         ; _∼_ = _⊆_
         ; isPreorder =
             record { isEquivalence = Setoid.isEquivalence (≡-Setoid _)
                    ; reflexive     = λ { {._} refl → ⊆-refl }
                    ; trans         = ⊆-trans } }

infix 3 _⊇_

_⊇_ : {I : Set} {X Y : I → Set} → (X ↝ Y) → (X ↝ Y) → Set
R ⊇ S = S ⊆ R

⊇-Preorder : {I : Set} (X Y : I → Set) → Preorder _ _ _
⊇-Preorder X Y = ConversePreorder (⊆-Preorder X Y)

⊆-Setoid : {I : Set} {X Y : I → Set} (R S : X ↝ Y) → Setoid _ _
⊆-Setoid {I} {X} {Y} R S =
  record { Carrier = R ⊆ S
         ; _≈_ = λ inc inc' → (i : I) (x : X i) (y : Y i) → modus-ponens-⊆ inc i x y ≐ modus-ponens-⊆ inc' i x y
         ; isEquivalence =
             record { refl  = λ i x y → frefl
                    ; sym   = λ eq i x y → fsym (eq i x y)
                    ; trans = λ eq eq' i x y → ftrans (eq i x y) (eq' i x y) } }

º-monotonic : {I : Set} {X Y : I → Set} {R S : X ↝ Y} → R ⊆ S → R º ⊆ S º
º-monotonic (wrap R⊆S) = wrap (º⁻-monotonic ∘ R⊆S)

•-monotonic : {I : Set} {X Y Z : I → Set} {R S : Y ↝ Z} {T U : X ↝ Y} → R ⊆ S → T ⊆ U → R • T ⊆ S • U
•-monotonic (wrap R⊆S) (wrap T⊆U) = wrap λ i → •⁻-monotonic (R⊆S i) (T⊆U i)

•-monotonic-l : {I : Set} {X Y Z : I → Set} {R S : X ↝ Y} (T : Y ↝ Z) → R ⊆ S → T • R ⊆ T • S
•-monotonic-l T = •-monotonic ⊆-refl

•-monotonic-r : {I : Set} {X Y Z : I → Set} {R S : X ↝ Y} (T : Z ↝ X) → R ⊆ S → R • T ⊆ S • T
•-monotonic-r T = flip •-monotonic ⊆-refl

≃-Setoid : {I : Set} (X Y : I → Set) → Setoid _ _
≃-Setoid X Y = PreorderSetoid (⊆-Preorder X Y)

infix 3 _≃_

_≃_ : {I : Set} {X Y : I → Set} → (X ↝ Y) → (X ↝ Y) → Set
_≃_ {I} {X} {Y} = Setoid._≈_ (≃-Setoid X Y)

≃-refl : {I : Set} {X Y : I → Set} {R : X ↝ Y} → R ≃ R
≃-refl {I} {X} {Y} = Setoid.refl (≃-Setoid X Y)

≃-sym : {I : Set} {X Y : I → Set} {R S : X ↝ Y} → R ≃ S → S ≃ R
≃-sym {I} {X} {Y} = Setoid.sym (≃-Setoid X Y)

≃-trans : {I : Set} {X Y : I → Set} {R S T : X ↝ Y} → R ≃ S → S ≃ T → R ≃ T
≃-trans {I} {X} {Y} = Setoid.trans (≃-Setoid X Y)

fun-preserves-comp : {I : Set} {X Y Z : I → Set} (f : Y ⇉ Z) (g : X ⇉ Y) → fun (λ {i} → f {i} ∘ g {i}) ≃ fun f • fun g
fun-preserves-comp f g = wrap (λ i → proj₁ (fun⁻-preserves-comp (f {i}) (g {i}))) , wrap (λ i → proj₂ (fun⁻-preserves-comp (f {i}) (g {i})))

º-preserves-idR : {I : Set} {X : I → Set} → idR º ≃ idR {I} {X}
º-preserves-idR = wrap (λ i → proj₁ º⁻-preserves-idR⁻) , wrap (λ i → proj₂ º⁻-preserves-idR⁻)

º-preserves-comp : {I : Set} {X Y Z : I → Set} (R : Y ↝ Z) (S : X ↝ Y) → (R • S) º ≃ S º • R º
º-preserves-comp R S = wrap (λ i → proj₁ (º⁻-preserves-comp ((R !!) i) ((S !!) i))) , wrap (λ i → proj₂ (º⁻-preserves-comp ((R !!) i) ((S !!) i)))

fun-cong : {I : Set} {X Y : I → Set} {f g : X ⇉ Y} → (∀ i → f {i} ≐ g {i}) → fun f ≃ fun g
fun-cong f≐g = wrap (λ i → proj₁ (fun⁻-cong (f≐g i))) , wrap (λ i → proj₂ (fun⁻-cong (f≐g i)))

fun-simple : {I : Set} {X Y : I → Set} (f : X ⇉ Y) → fun f • fun f º ⊆ idR
fun-simple f = wrap λ i → fun⁻-simple (f {i})

fun-entire : {I : Set} {X Y : I → Set} (f : X ⇉ Y) → idR ⊆ fun f º • fun f
fun-entire f = wrap λ i → fun⁻-entire (f {i})

º-cong : {I : Set} {X Y : I → Set} {R S : X ↝ Y} → R ≃ S → R º ≃ S º
º-cong (R⊆S , R⊇S) = º-monotonic R⊆S , º-monotonic R⊇S

idR-l : {I : Set} {X Y : I → Set} (R : X ↝ Y) → idR • R ≃ R
idR-l R = wrap (λ i → proj₁ (idR⁻-l ((R !!) i))) , wrap (λ i → proj₂ (idR⁻-l ((R !!) i)))

idR-r : {I : Set} {X Y : I → Set} (R : X ↝ Y) → R • idR ≃ R
idR-r R = wrap (λ i → proj₁ (idR⁻-r ((R !!) i))) , wrap (λ i → proj₂ (idR⁻-r ((R !!) i)))

•-cong : {I : Set} {X Y Z : I → Set} {R S : Y ↝ Z} {T U : X ↝ Y} → R ≃ S → T ≃ U → R • T ≃ S • U
•-cong (R⊆S , R⊇S) (T⊆U , T⊇U) = •-monotonic R⊆S T⊆U , •-monotonic R⊇S T⊇U

•-cong-l : {I : Set} {X Y Z : I → Set} {R S : X ↝ Y} (T : Y ↝ Z) → R ≃ S → T • R ≃ T • S
•-cong-l T = •-cong ≃-refl

•-cong-r : {I : Set} {X Y Z : I → Set} {R S : X ↝ Y} (T : Z ↝ X) → R ≃ S → R • T ≃ S • T
•-cong-r T = flip •-cong ≃-refl

•-assoc : {I : Set} {X Y Z W : I → Set} (R : Z ↝ W) (S : Y ↝ Z) (T : X ↝ Y) → (R • S) • T ≃ R • (S • T)
•-assoc R S T = wrap (λ i → proj₁ (•⁻-assoc ((R !!) i) ((S !!) i) ((T !!) i))) , wrap (λ i → proj₂ (•⁻-assoc ((R !!) i) ((S !!) i) ((T !!) i)))

iso-conv : {I : Set} {X Y : I → Set} → (isos : ∀ i → Iso Fun (X i) (Y i)) →
            fun (λ {i} → Iso.to (isos i)) º ≃ fun (λ {i} → Iso.from (isos i))
iso-conv isos = wrap (λ i → proj₁ (iso⁻-conv (isos i))) , wrap (λ i → proj₂ (iso⁻-conv (isos i)))

iso-idR : {I : Set} {X Y : I → Set} → (isos : ∀ i → Iso Fun (X i) (Y i)) →
           fun (λ {i} → Iso.to (isos i)) • fun (λ {i} → Iso.to (isos i)) º ≃ idR
iso-idR {Y = Y} isos = wrap (λ i → proj₁ (iso⁻-idR⁻ (isos i))) , wrap (λ i → proj₂ (iso⁻-idR⁻ (isos i)))

fun-shunting-l-⇒ : {I : Set} {X Y Z : I → Set} (f : Y ⇉ Z) (R : X ↝ Y) (S : X ↝ Z) → fun f • R ⊆ S → R ⊆ fun f º • S
fun-shunting-l-⇒ f R S (wrap f•R⊆S) = wrap λ i → fun⁻-shunting-l-⇒ (f {i}) ((R !!) i) ((S !!) i) (f•R⊆S i)

fun-shunting-l-⇐ : {I : Set} {X Y Z : I → Set} (f : Y ⇉ Z) (R : X ↝ Y) (S : X ↝ Z) → R ⊆ fun f º • S → fun f • R ⊆ S
fun-shunting-l-⇐ f R S (wrap R⊆fº•S) = wrap λ i → fun⁻-shunting-l-⇐ (f {i}) ((R !!) i) ((S !!) i) (R⊆fº•S i)

fun-shunting-r-⇒ : {I : Set} {X Y Z : I → Set} (f : Y ⇉ X) (R : Y ↝ Z) (S : X ↝ Z) → R • fun f º ⊆ S → R ⊆ S • fun f
fun-shunting-r-⇒ f R S (wrap R•fº⊆S) = wrap λ i → fun⁻-shunting-r-⇒ (f {i}) ((R !!) i) ((S !!) i) (R•fº⊆S i)

fun-shunting-r-⇐ : {I : Set} {X Y Z : I → Set} (f : Y ⇉ X) (R : Y ↝ Z) (S : X ↝ Z) → R ⊆ S • fun f → R • fun f º ⊆ S
fun-shunting-r-⇐ f R S (wrap R⊆f•S) = wrap λ i → fun⁻-shunting-r-⇐ (f {i}) ((R !!) i) ((S !!) i) (R⊆f•S i)


--------
-- functorial map

Ṗ-mapR : {I : Set} {X Y : I → Set} → (X ↝ Y) → (is : List I) → Ṗ is X ↝⁻ Ṗ is Y
Ṗ-mapR R []       _        = any
Ṗ-mapR R (i ∷ is) (x , xs) = map℘₂ _,_ ((R !!) i x) (Ṗ-mapR R is xs)

Ṗ-mapR-monotonic : {I : Set} {X Y : I → Set} {R S : X ↝ Y} → R ⊆ S → (is : List I) → Ṗ-mapR R is ⊆⁻ Ṗ-mapR S is
Ṗ-mapR-monotonic R⊆S []       = ⊆⁻-refl
Ṗ-mapR-monotonic R⊆S (i ∷ is) = wrap λ { (x , xs) → map℘₂-monotonic _,_ (modus-ponens-⊆ R⊆S _ x)
                                                                        (modus-ponens-⊆⁻ (Ṗ-mapR-monotonic R⊆S is) xs) }

Ṗ-mapR-preserves-comp-⊇⁻ : {I : Set} {X Y Z : I → Set} (R : Y ↝ Z) (S : X ↝ Y) (is : List I) → Ṗ-mapR (R • S) is ⊇⁻ Ṗ-mapR R is •⁻ Ṗ-mapR S is
Ṗ-mapR-preserves-comp-⊇⁻ R S []       = wrap λ _ _ _ → tt
Ṗ-mapR-preserves-comp-⊇⁻ R S (i ∷ is) = wrap λ { (x , xs) (z , zs) ((y , ys) , (._ , s , ._ , ss , refl) , (._ , r , ._ , rs , refl)) →
                                                let rss = modus-ponens-⊆⁻ (Ṗ-mapR-preserves-comp-⊇⁻ R S is) xs zs (ys , ss , rs)
                                                in  z , (y , s , r) , zs , rss , refl }

Ṗ-mapR-preserves-comp-⊆⁻ : {I : Set} {X Y Z : I → Set} (R : Y ↝ Z) (S : X ↝ Y) (is : List I) → Ṗ-mapR (R • S) is ⊆⁻ Ṗ-mapR R is •⁻ Ṗ-mapR S is
Ṗ-mapR-preserves-comp-⊆⁻ R S []       = wrap λ _ _ _ → tt , tt , tt
Ṗ-mapR-preserves-comp-⊆⁻ R S (i ∷ is) = wrap λ { (x , xs) (z , zs) (.z , (y , s , r) , .zs , rss , refl) →
                                                let (ys , ss , rs) = modus-ponens-⊆⁻ (Ṗ-mapR-preserves-comp-⊆⁻ R S is) xs zs rss
                                                in  (y , ys) , (y , s , ys , ss , refl) , (z , r , zs , rs , refl) }

Ṗ-mapR-preserves-conv :
  {I : Set} {X Y : I → Set} (R : X ↝ Y) (is : List I) (xs : Ṗ is X) (ys : Ṗ is Y) → Ṗ-mapR R is xs ys → Ṗ-mapR (R º) is ys xs
Ṗ-mapR-preserves-conv R []       _        _        _                         = tt
Ṗ-mapR-preserves-conv R (i ∷ is) (x , xs) (y , ys) (._ , r , ._ , rs , refl) = x , r , xs , Ṗ-mapR-preserves-conv R is xs ys rs , refl

mapR : {I : Set} (D : RDesc I) {X Y : I → Set} → (X ↝ Y) → ⟦ D ⟧ X ↝⁻ ⟦ D ⟧ Y
mapR (ṿ is)  R xs       = Ṗ-mapR R is xs
mapR (σ S D) R (s , xs) = map℘ (_,_ s) (mapR (D s) R xs)

mapR-monotonic : {I : Set} (D : RDesc I) {X Y : I → Set} {R S : X ↝ Y} → R ⊆ S → mapR D R ⊆⁻ mapR D S
mapR-monotonic (ṿ is)  R⊆S = Ṗ-mapR-monotonic R⊆S is
mapR-monotonic (σ S D) R⊆S = wrap λ { (s , xs) → map℘-monotonic (_,_ s) (modus-ponens-⊆⁻ (mapR-monotonic (D s) R⊆S) xs) }

Ṗ-mapR-fun⁻-computation : {I : Set} {X Y : I → Set} (f : X ⇉ Y) (is : List I) (xs : Ṗ is X) → Ṗ-mapR (fun f) is xs (Ṗ-map f is xs)
Ṗ-mapR-fun⁻-computation f []       _        = tt
Ṗ-mapR-fun⁻-computation f (i ∷ is) (x , xs) = f x , refl , Ṗ-map f is xs , Ṗ-mapR-fun⁻-computation f is xs , refl

Ṗ-mapR-fun⁻-unique :
  {I : Set} {X Y : I → Set} (f : X ⇉ Y) (is : List I) (xs : Ṗ is X) (ys : Ṗ is Y) → Ṗ-mapR (fun f) is xs ys → Ṗ-map f is xs ≡ ys
Ṗ-mapR-fun⁻-unique f []       _        _             _                             = refl
Ṗ-mapR-fun⁻-unique f (i ∷ is) (x , xs) (.(f x) , ys) (._ , refl , ._ , eqs , refl) = cong₂ _,_ refl (Ṗ-mapR-fun⁻-unique f is xs ys eqs)

mapR-preserves-comp-⊆⁻ : {I : Set} (D : RDesc I) {X Y Z : I → Set} (R : Y ↝ Z) (S : X ↝ Y) → mapR D (R • S) ⊆⁻ mapR D R •⁻ mapR D S
mapR-preserves-comp-⊆⁻ (ṿ is)  R S = Ṗ-mapR-preserves-comp-⊆⁻ R S is
mapR-preserves-comp-⊆⁻ (σ T D) R S = wrap λ { (t , xs) ._ (zs , rss , refl) →
                                             let (ys , ss , rs) = modus-ponens-⊆⁻ (mapR-preserves-comp-⊆⁻ (D t) R S) xs zs rss
                                             in  (t , ys) , (ys , ss , refl) , (zs , rs , refl) }

mapR-preserves-comp-⊇⁻ : {I : Set} (D : RDesc I) {X Y Z : I → Set} (R : Y ↝ Z) (S : X ↝ Y) → mapR D (R • S) ⊇⁻ mapR D R •⁻ mapR D S
mapR-preserves-comp-⊇⁻ (ṿ is)  R S = Ṗ-mapR-preserves-comp-⊇⁻ R S is
mapR-preserves-comp-⊇⁻ (σ T D) R S = wrap λ { (t , xs) ._ (._ , (ys , ss , refl) , (zs , rs , refl)) →
                                             zs , modus-ponens-⊆⁻ (mapR-preserves-comp-⊇⁻ (D t) R S) xs zs (ys , ss , rs) , refl }

mapR-preserves-conv : {I : Set} (D : RDesc I) {X Y : I → Set} (R : X ↝ Y) → (xs : ⟦ D ⟧ X) (ys : ⟦ D ⟧ Y) → mapR D R xs ys → mapR D (R º) ys xs
mapR-preserves-conv (ṿ is)  R xs       ys rs               = Ṗ-mapR-preserves-conv R is xs ys rs
mapR-preserves-conv (σ S D) R (s , xs) ._ (ys , rs , refl) = xs , mapR-preserves-conv (D s) R xs ys rs , refl

mapR-fun⁻-computation : {I : Set} (D : RDesc I) {X Y : I → Set} (f : X ⇉ Y) → (xs : ⟦ D ⟧ X) → mapR D (fun f) xs (mapF D f xs)
mapR-fun⁻-computation (ṿ is)  f xs       = Ṗ-mapR-fun⁻-computation f is xs
mapR-fun⁻-computation (σ S D) f (s , xs) = mapF (D s) f xs , mapR-fun⁻-computation (D s) f xs , refl

mapR-fun⁻-unique : {I : Set} (D : RDesc I) {X Y : I → Set} (f : X ⇉ Y) → (xs : ⟦ D ⟧ X) (ys : ⟦ D ⟧ Y) → mapR D (fun f) xs ys → mapF D f xs ≡ ys
mapR-fun⁻-unique (ṿ is)  f xs         ys         eqs                = Ṗ-mapR-fun⁻-unique f is xs ys eqs
mapR-fun⁻-unique (σ S D) f (s , xs)   (.s , ys)  (.ys , eqs , refl) = cong (_,_ s) (mapR-fun⁻-unique (D s) f xs ys eqs)


--------
-- relators

Ṙ : {I : Set} (D : Desc I) {X Y : I → Set} → (X ↝ Y) → Ḟ D X ↝ Ḟ D Y
Ṙ D R = wrap λ i → mapR (Desc.comp D i) R

Ṙ-monotonic : {I : Set} (D : Desc I) {X Y : I → Set} {R S : X ↝ Y} → R ⊆ S → Ṙ D R ⊆ Ṙ D S
Ṙ-monotonic D R⊆S = wrap λ i → mapR-monotonic (Desc.comp D i) R⊆S

Ṙ-cong : {I : Set} (D : Desc I) {X Y : I → Set} {R S : X ↝ Y} → R ≃ S → Ṙ D R ≃ Ṙ D S
Ṙ-cong D (R⊆S , R⊇S) = Ṙ-monotonic D R⊆S , Ṙ-monotonic D R⊇S

Ṙ-preserves-comp : {I : Set} (D : Desc I) {X Y Z : I → Set} (R : Y ↝ Z) (S : X ↝ Y) → Ṙ D (R • S) ≃ Ṙ D R • Ṙ D S
Ṙ-preserves-comp D R S = wrap (λ i → mapR-preserves-comp-⊆⁻ (Desc.comp D i) R S) , wrap (λ i → mapR-preserves-comp-⊇⁻ (Desc.comp D i) R S)

Ṙ-preserves-conv : {I : Set} (D : Desc I) {X Y : I → Set} (R : X ↝ Y) → Ṙ D (R º) ≃ Ṙ D R º
Ṙ-preserves-conv D R = wrap (λ i → wrap λ ys xs → mapR-preserves-conv (Desc.comp D i) (R º) ys xs) ,
                       wrap (λ i → wrap λ ys xs → mapR-preserves-conv (Desc.comp D i)  R     xs ys)

fun⁻-preserves-map : {I : Set} (D : Desc I) {X Y : I → Set} (f : X ⇉ Y) → fun (Ḟ-map D (λ {i} → f {i})) ≃ Ṙ D (fun f)
fun⁻-preserves-map D f = wrap (λ i → wrap λ { xs ._ refl → mapR-fun⁻-computation (Desc.comp D i) f xs }) ,
                        wrap (λ i → wrap λ xs → mapR-fun⁻-unique (Desc.comp D i) f xs)

Ṙ-preserves-idR : {I : Set} (D : Desc I) {X : I → Set} → Ṙ D (idR {I} {X}) ≃ idR
Ṙ-preserves-idR D {X} =
  begin
    Ṙ D idR
      ≃⟨ Setoid.sym setoid (fun⁻-preserves-map D id) ⟩
    fun (Ḟ-map D id)
      ≃⟨ fun-cong (Ḟ-map-preserves-id D) ⟩
    idR
  □
  where setoid = ≃-Setoid (Ḟ D X) (Ḟ D X)
        open EqReasoning setoid renaming (_≈⟨_⟩_ to _≃⟨_⟩_; _∎ to _□)

fun-monotonic-alg-lemma :
 {I : Set} (D : Desc I) {X : I → Set} (f : Ḟ D X ⇉ X) (R : X ↝ X) → fun f • Ṙ D R ⊆ R • fun f → fun f • Ṙ D (R º) ⊆ R º • fun f
fun-monotonic-alg-lemma D f R =
  begin
    fun f • Ṙ D R ⊆ R • fun f
      ⇒⟨ º-monotonic ⟩
    (fun f • Ṙ D R) º ⊆ (R • fun f) º
      ⇒⟨ ⊆-trans (proj₂ (º-preserves-comp (fun f) (Ṙ D R))) ⟩
    Ṙ D R º • fun f º ⊆ (R • fun f) º
      ⇒⟨ ⊆-trans (•-monotonic-r (fun f º) (proj₁ (Ṙ-preserves-conv D R))) ⟩
    Ṙ D (R º) • fun f º ⊆ (R • fun f) º
      ⇒⟨ flip ⊆-trans (proj₁ (º-preserves-comp R (fun f))) ⟩
    Ṙ D (R º) • fun f º ⊆ fun f º • R º
      ⇒⟨ fun-shunting-l-⇐ f (Ṙ D (R º) • fun f º) (R º) ⟩
    fun f • Ṙ D (R º) • fun f º ⊆ R º
      ⇒⟨ ⊆-trans (proj₁ (•-assoc (fun f) (Ṙ D (R º)) (fun f º))) ⟩
    (fun f • Ṙ D (R º)) • fun f º ⊆ R º
      ⇒⟨ fun-shunting-r-⇒ f (fun f • Ṙ D (R º)) (R º) ⟩
    fun f • Ṙ D (R º) ⊆ R º • fun f
  □
  where open PreorderReasoning ⇒-Preorder renaming (_∼⟨_⟩_ to _⇒⟨_⟩_; _∎ to _□)
