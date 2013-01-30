-- Basic definitions of subsets and relations, combinators for specifying nondeterministic computation,
-- subset and relational inclusion wrapped up as preorder and setoid, combinators for reasoning with relations,
-- componentwise relations between families of sets, definition of join of componentwise relations,
-- and definition and properties of relators.

module Thesis.Relation where

open import Thesis.Prelude.Category.Isomorphism
open import Thesis.Prelude.Function
open import Thesis.Prelude.Function.Fam
open import Thesis.Description

open import Function using (id; _∘_; flip; type-signature)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary using (Setoid; Preorder)
import Relation.Binary.EqReasoning as EqReasoning
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym; trans) renaming (setoid to ≡-Setoid)


--------
-- subsets

℘ : Set → Set₁
℘ A = A → Set

return : {A : Set} → A → ℘ A
return = _≡_

_>>=_ : {A B : Set} → (S : ℘ A) → (A → ℘ B) → ℘ B
_>>=_ {A} S f = λ y → Σ[ x ∶ A ] S x × f x y

map℘ : {A B : Set} → (A → B) → ℘ A → ℘ B
map℘ f s = s >>= (return ∘ f)

map℘₂ : {A B C : Set} → (A → B → C) → ℘ A → ℘ B → ℘ C
map℘₂ f s t = s >>= λ x → t >>= λ y → return (f x y)

-- ∀ y. (return x >>= f) y ⇔ f x y
-- ∀ y. (s >>= return) y ⇔ s y

any : {A : Set} → ℘ A
any _ = ⊤

any>>=_ : {A B : Set} → (A → ℘ B) → ℘ B
any>>=_ {A} f = λ y → Σ[ x ∶ A ] f x y

infix 2 any>>=_

none : {A : Set} → ℘ A
none _ = ⊥


--------
-- relations

_↝_ : Set → Set → Set₁
X ↝ Y = X → ℘ Y

fun : {X Y : Set} → (X → Y) → X ↝ Y
fun f = return ∘ f

idR : {X : Set} → X ↝ X
idR = fun id

infix 6 _º

_º : {X Y : Set} → (X ↝ Y) → Y ↝ X
R º = flip R

infixr 4 _•_

_•_ : {X Y Z : Set} → (Y ↝ Z) → (X ↝ Y) → X ↝ Z
R • S = λ x → S x >>= R


--------
-- subset inclusion

infix 1 _⊑_

record _⊑_ {A : Set} (s t : ℘ A) : Set where
  constructor wrap
  field
    comp : ∀ x → s x → t x

modus-ponens-⊑ : {A : Set} {s t : ℘ A} → s ⊑ t → ∀ x → s x → t x
modus-ponens-⊑ = _⊑_.comp

_⊒_ : {A : Set} → ℘ A → ℘ A → Set
s ⊒ t = t ⊑ s

⊑-refl : {A : Set} {s : ℘ A} → s ⊑ s
⊑-refl = wrap λ _ → id

⊑-trans : {A : Set} {s t u : ℘ A} → s ⊑ t → t ⊑ u → s ⊑ u
⊑-trans (wrap s⊑t) (wrap t⊑u) = wrap λ a → t⊑u a ∘ s⊑t a

map℘-monotonic : {A B : Set} {s t : ℘ A} (f : A → B) → s ⊑ t → map℘ f s ⊑ map℘ f t
map℘-monotonic f (wrap s⊑t) = wrap λ { b (a , sa , eq) → a , s⊑t a sa , eq }

map℘₂-monotonic : {A B C : Set} {s t : ℘ A} {u v : ℘ B} (f : A → B → C) → s ⊑ t → u ⊑ v → map℘₂ f s u ⊑ map℘₂ f t v
map℘₂-monotonic f (wrap s⊑t) (wrap u⊑v) = wrap λ { c (a , sa , b , ub , eq) → a , s⊑t a sa , b , u⊑v b ub , eq }

⊑-Preorder : (A : Set) → Preorder _ _ _
⊑-Preorder A =
  record { Carrier = ℘ A
         ; _≈_ = _≡_
         ; _∼_ = _⊑_
         ; isPreorder =
             record { isEquivalence = Setoid.isEquivalence (≡-Setoid _)
                    ; reflexive     = λ { {._} refl → ⊑-refl }
                    ; trans         = ⊑-trans } }


--------
-- relational inclusion

infix 3 _⊆_

record _⊆_ {X Y : Set} (R S : X ↝ Y) : Set where
  constructor wrap
  field
    comp : (x : X) (y : Y) → R x y → S x y

modus-ponens-⊆ : {X Y : Set} {R S : X ↝ Y} → R ⊆ S → (x : X) (y : Y) → R x y → S x y
modus-ponens-⊆ = _⊆_.comp

infix 3 _⊇_

_⊇_ : {X Y : Set} → (X ↝ Y) → (X ↝ Y) → Set
R ⊇ S = S ⊆ R

⊆-refl : {X Y : Set} {R : X ↝ Y} → R ⊆ R
⊆-refl = wrap λ _ _ → id

⊆-trans : {X Y : Set} {R S T : X ↝ Y} → R ⊆ S → S ⊆ T → R ⊆ T
⊆-trans (wrap R⊆S) (wrap S⊆T) = wrap λ x y → S⊆T x y ∘ R⊆S x y

⊆-Preorder : (X Y : Set) → Preorder _ _ _
⊆-Preorder X Y =
  record { Carrier = X ↝ Y
         ; _≈_ = _≡_
         ; _∼_ = _⊆_
         ; isPreorder =
             record { isEquivalence = Setoid.isEquivalence (≡-Setoid _)
                    ; reflexive     = λ { {._} refl → ⊆-refl }
                    ; trans         = ⊆-trans } }

⊇-Preorder : (X Y : Set) → Preorder _ _ _
⊇-Preorder X Y =
  record { Carrier = X ↝ Y
         ; _≈_ = _≡_
         ; _∼_ = _⊇_
         ; isPreorder =
             record { isEquivalence = Setoid.isEquivalence (≡-Setoid _)
                    ; reflexive     = λ { {._} refl → ⊆-refl }
                    ; trans         = flip ⊆-trans } }

º-monotonic : {X Y : Set} {R S : X ↝ Y} → R ⊆ S → R º ⊆ S º
º-monotonic (wrap R⊆S) = wrap λ y x r → R⊆S x y r

•-monotonic : {X Y Z : Set} {R S : Y ↝ Z} {T U : X ↝ Y} → R ⊆ S → T ⊆ U → R • T ⊆ S • U
•-monotonic (wrap R⊆S) (wrap T⊆U) = wrap λ { x z (y , t , r) → y , T⊆U x y t , R⊆S y z r }

•-monotonic-l : {X Y Z : Set} {R S : X ↝ Y} (T : Y ↝ Z) → R ⊆ S → T • R ⊆ T • S
•-monotonic-l T = •-monotonic ⊆-refl

•-monotonic-r : {X Y Z : Set} {R S : X ↝ Y} (T : Z ↝ X) → R ⊆ S → R • T ⊆ S • T
•-monotonic-r T = flip •-monotonic ⊆-refl


--------
-- relational bi-inclusion

infix 3 _≃_

_≃_ : {X Y : Set} → (X ↝ Y) → (X ↝ Y) → Set
R ≃ S = (R ⊆ S) × (R ⊇ S)

≃-refl : {X Y : Set} {R : X ↝ Y} → R ≃ R
≃-refl = ⊆-refl , ⊆-refl

≃-sym : {X Y : Set} {R S : X ↝ Y} → R ≃ S → S ≃ R
≃-sym (R⊆S , R⊇S) = R⊇S , R⊆S

≃-trans : {X Y : Set} {R S T : X ↝ Y} → R ≃ S → S ≃ T → R ≃ T
≃-trans (R⊆S , R⊇S) (S⊆T , S⊇T) = ⊆-trans R⊆S S⊆T , ⊆-trans S⊇T R⊇S

≃-Setoid : (X Y : Set) → Setoid _ _
≃-Setoid X Y =
  record { Carrier = X ↝ Y
         ; _≈_ = _≃_
         ; isEquivalence = record { refl = ≃-refl; sym = ≃-sym; trans = ≃-trans } }

fun-preserves-comp : {X Y Z : Set} (f : Y → Z) (g : X → Y) → fun (f ∘ g) ≃ fun f • fun g
fun-preserves-comp f g = wrap (λ { x ._ refl → g x , refl , refl }) , wrap (λ { x ._ (._ , refl , refl) → refl })

º-preserves-comp : {X Y Z : Set} (R : Y ↝ Z) (S : X ↝ Y) → (R • S) º ≃ S º • R º
º-preserves-comp R S = wrap (λ { z x (y , s , r) → y , r , s }) , wrap (λ { z x (y , r , s) → y , s , r })

fun-cong : {X Y : Set} {f g : X → Y} → f ≐ g → fun f ≃ fun g
fun-cong f≐g = wrap (λ { x ._ refl → fsym f≐g x }) , wrap (λ { x ._ refl → f≐g x })

º-cong : {X Y : Set} {R S : X ↝ Y} → R ≃ S → R º ≃ S º
º-cong (R⊆S , R⊇S) = º-monotonic R⊆S , º-monotonic R⊇S

idR-l : {X Y : Set} (R : X ↝ Y) → idR • R ≃ R
idR-l R = (wrap λ { x y (.y , r , refl) → r }) , wrap (λ x y r → y , r , refl)

idR-r : {X Y : Set} (R : X ↝ Y) → R • idR ≃ R
idR-r R = (wrap λ { x y (.x , refl , r) → r }) , wrap (λ x y r → x , refl , r)

•-cong : {X Y Z : Set} {R S : Y ↝ Z} {T U : X ↝ Y} → R ≃ S → T ≃ U → R • T ≃ S • U
•-cong (R⊆S , R⊇S) (T⊆U , T⊇U) = •-monotonic R⊆S T⊆U , •-monotonic R⊇S T⊇U

•-cong-l : {X Y Z : Set} {R S : X ↝ Y} (T : Y ↝ Z) → R ≃ S → T • R ≃ T • S
•-cong-l T = •-cong ≃-refl

•-cong-r : {X Y Z : Set} {R S : X ↝ Y} (T : Z ↝ X) → R ≃ S → R • T ≃ S • T
•-cong-r T = flip •-cong ≃-refl

•-assoc : {X Y Z W : Set} (R : Z ↝ W) (S : Y ↝ Z) (T : X ↝ Y) → (R • S) • T ≃ R • (S • T)
•-assoc R S T = wrap (λ { x w (y , t , z , s , r) → z , (y , t , s) , r }) , wrap (λ { x w (z , (y , t , s) , r) → y , t , z , s , r })

iso-conv : {X Y : Set} → (iso : Iso Fun X Y) → fun (Iso.to Fun iso) º ≃ fun (Iso.from Fun iso)
iso-conv iso =
  (wrap (λ y x eq → trans (sym (cong (from iso) eq)) (from-to-inverse iso x))) ,
  (wrap (λ y x eq → trans (sym (cong (to   iso) eq)) (to-from-inverse iso y)))
  where open Iso Fun

iso-idR : {X Y : Set} → (iso : Iso Fun X Y) →
            fun (Iso.to Fun iso) • fun (Iso.to Fun iso) º ≃ idR
iso-idR {Y = Y} iso =
  begin
    fun (Iso.to Fun iso) • fun (Iso.to Fun iso) º
      ≃⟨ •-cong-l (fun (Iso.to Fun iso)) (iso-conv iso) ⟩
    fun (Iso.to Fun iso) • fun (Iso.from Fun iso)
      ≃⟨ Setoid.sym setoid (fun-preserves-comp (Iso.to Fun iso) (Iso.from Fun iso)) ⟩
    fun (Iso.to Fun iso ∘ Iso.from Fun iso)
      ≃⟨ fun-cong (Iso.to-from-inverse Fun iso) ⟩
    idR
  □
  where setoid = ≃-Setoid Y Y
        open EqReasoning setoid renaming (_≈⟨_⟩_ to _≃⟨_⟩_; _∎ to _□)


--------
-- componentwise relations between families of sets

_↝⁺_ : {I : Set} → (I → Set) → (I → Set) → Set₁
X ↝⁺ Y = ∀ i → X i ↝ Y i

fun⁺ : {I : Set} {X Y : I → Set} → (X ⇒ Y) → X ↝⁺ Y
fun⁺ f i = fun (f {i})

α : {I : Set} {D : Desc I} → Ḟ D (μ D) ↝⁺ μ D
α = fun⁺ con

_º⁺ : {I : Set} {X Y : I → Set} → X ↝⁺ Y → Y ↝⁺ X
(R º⁺) i = R i º

_•⁺_ : {I : Set} {X Y Z : I → Set} → Y ↝⁺ Z → X ↝⁺ Y → X ↝⁺ Z
(R •⁺ S) i = R i • S i

infix 3 _⊆⁺_

_⊆⁺_ : {I : Set} {X Y : I → Set} → (X ↝⁺ Y) → (X ↝⁺ Y) → Set
R ⊆⁺ S = ∀ i → R i ⊆ S i

⊆⁺-refl : {I : Set} {X Y : I → Set} {R : X ↝⁺ Y} → R ⊆⁺ R
⊆⁺-refl i = ⊆-refl

⊆⁺-trans : {I : Set} {X Y : I → Set} {R S T : X ↝⁺ Y} → R ⊆⁺ S → S ⊆⁺ T → R ⊆⁺ T
⊆⁺-trans R⊆⁺S S⊆⁺T i = ⊆-trans (R⊆⁺S i) (S⊆⁺T i)

⊆⁺-Preorder : {I : Set} (X Y : I → Set) → Preorder _ _ _
⊆⁺-Preorder X Y =
  record { Carrier = X ↝⁺ Y
         ; _≈_ = _≡_
         ; _∼_ = _⊆⁺_
         ; isPreorder =
             record { isEquivalence = Setoid.isEquivalence (≡-Setoid _)
                    ; reflexive     = λ { {._} refl → ⊆⁺-refl }
                    ; trans         = ⊆⁺-trans } }

infix 3 _≃⁺_
_≃⁺_ : {I : Set} {X Y : I → Set} → (X ↝⁺ Y) → (X ↝⁺ Y) → Set
R ≃⁺ S = ∀ i → R i ≃ S i

≃⁺-refl : {I : Set} {X Y : I → Set} {R : X ↝⁺ Y} → R ≃⁺ R
≃⁺-refl i = ⊆-refl , ⊆-refl

≃⁺-sym : {I : Set} {X Y : I → Set} {R S : X ↝⁺ Y} → R ≃⁺ S → S ≃⁺ R
≃⁺-sym R≃⁺S i = proj₂ (R≃⁺S i) , proj₁ (R≃⁺S i)

≃⁺-trans : {I : Set} {X Y : I → Set} {R S T : X ↝⁺ Y} → R ≃⁺ S → S ≃⁺ T → R ≃⁺ T
≃⁺-trans R≃⁺S S≃⁺T i = ⊆-trans (proj₁ (R≃⁺S i)) (proj₁ (S≃⁺T i)) , ⊆-trans (proj₂ (S≃⁺T i)) (proj₂ (R≃⁺S i))

≃⁺-Setoid : {I : Set} (X Y : I → Set) → Setoid _ _
≃⁺-Setoid X Y =
  record { Carrier = X ↝⁺ Y
         ; _≈_ = _≃⁺_
         ; isEquivalence = record { refl = ≃⁺-refl; sym = ≃⁺-sym; trans = ≃⁺-trans } }


--------
-- componentwise join

⋃ : {I : Set} {X Y : I → Set} (R : X ↝⁺ Y) → Σ I X ↝ Σ I Y
⋃ R (i , x) = map℘ (_,_ i) (R i x)

infix 7 _!!

_!! : {I : Set} {X Y : I → Set} → (R : Σ I X ↝ Σ I Y) → X ↝⁺ Y
(R !!) i x y = R (i , x) (i , y)


⋃-universal-⇒ : {I : Set} {X Y : I → Set} (R : X ↝⁺ Y) (S : Σ I X ↝ Σ I Y) → ⋃ R ⊆ S → R ⊆⁺ S !!
⋃-universal-⇒ R S (wrap ⋃R⊆S) i = wrap λ x y r → ⋃R⊆S (i , x) (i , y) (y , r , refl)

⋃-universal-⇐ : {I : Set} {X Y : I → Set} (R : X ↝⁺ Y) (S : Σ I X ↝ Σ I Y) → R ⊆⁺ S !! → ⋃ R ⊆ S
⋃-universal-⇐ R S R⊆⁺S!! = wrap λ { (i , x) ._ (y , r , refl) → modus-ponens-⊆ (R⊆⁺S!! i) x y r }


--------
-- functorial map

mapR : {I : Set} (D : RDesc I) {X Y : I → Set} → (X ↝⁺ Y) → ⟦ D ⟧ X ↝ ⟦ D ⟧ Y
mapR ∎       R xs         = any
mapR (ṿ i)   R x          = R i x
mapR (σ S D) R (s , xs)   = map℘ (_,_ s) (mapR (D s) R xs)
mapR (D * E) R (xs , xs') = map℘₂ _,_ (mapR D R xs) (mapR E R xs')

mapR-monotonic : {I : Set} (D : RDesc I) {X Y : I → Set} {R S : X ↝⁺ Y} → R ⊆⁺ S → mapR D R ⊆ mapR D S
mapR-monotonic ∎       R⊆⁺S = ⊆-refl
mapR-monotonic (ṿ i)   R⊆⁺S = R⊆⁺S i
mapR-monotonic (σ S D) R⊆⁺S = wrap λ { (s , xs) ._ (ys , rs , refl) → ys , modus-ponens-⊆ (mapR-monotonic (D s) R⊆⁺S) xs ys rs , refl }
mapR-monotonic (D * E) R⊆⁺S =
  wrap λ { (xs , xs') ._ (ys , rs , ys' , rs' , refl) →
           ys , modus-ponens-⊆ (mapR-monotonic D R⊆⁺S) xs ys rs , ys' , modus-ponens-⊆ (mapR-monotonic E R⊆⁺S) xs' ys' rs' , refl }

mapR-preserves-comp-⊆ :
  {I : Set} (D : RDesc I) {X Y Z : I → Set} (R : Y ↝⁺ Z) (S : X ↝⁺ Y) → mapR D (R •⁺ S) ⊆ mapR D R • mapR D S
mapR-preserves-comp-⊆ ∎       R S = wrap λ _ _ _ → tt , tt , tt
mapR-preserves-comp-⊆ (ṿ i)   R S = ⊆-refl
mapR-preserves-comp-⊆ (σ T D) R S = wrap λ { (t , xs) ._ (zs , rss , refl) →
                                             let (ys , ss , rs) = modus-ponens-⊆ (mapR-preserves-comp-⊆ (D t) R S) xs zs rss
                                             in  (t , ys) , (ys , ss , refl) , (zs , rs , refl) }
mapR-preserves-comp-⊆ (D * E) R S = wrap λ { (xs , xs') ._ (zs , rss , zs' , rss' , refl) →
                                             let (ys  , ss  , rs ) = modus-ponens-⊆ (mapR-preserves-comp-⊆ D R S) xs  zs  rss
                                                 (ys' , ss' , rs') = modus-ponens-⊆ (mapR-preserves-comp-⊆ E R S) xs' zs' rss'
                                             in  (ys , ys') , (ys , ss , ys' , ss' , refl) , (zs , rs , zs' , rs' , refl) }

mapR-preserves-comp-⊇ :
  {I : Set} (D : RDesc I) {X Y Z : I → Set} (R : Y ↝⁺ Z) (S : X ↝⁺ Y) → mapR D (R •⁺ S) ⊇ mapR D R • mapR D S
mapR-preserves-comp-⊇ ∎       R S = wrap λ _ _ _ → tt
mapR-preserves-comp-⊇ (ṿ i)   R S = ⊆-refl
mapR-preserves-comp-⊇ (σ T D) R S = wrap λ { (t , xs) ._ (._ , (ys , ss , refl) , (zs , rs , refl)) →
                                             zs , modus-ponens-⊆ (mapR-preserves-comp-⊇ (D t) R S) xs zs (ys , ss , rs) , refl }
mapR-preserves-comp-⊇ (D * E) R S = wrap λ { (xs , xs') ._ (._ , (ys , ss , ys' , ss' , refl) , (zs , rs , zs' , rs' , refl)) →
                                             zs  , modus-ponens-⊆ (mapR-preserves-comp-⊇ D R S) xs  zs  (ys  , ss  ,  rs) ,
                                             zs' , modus-ponens-⊆ (mapR-preserves-comp-⊇ E R S) xs' zs' (ys' , ss' , rs') , refl }

mapR-preserves-conv :
  {I : Set} (D : RDesc I) {X Y : I → Set} (R : X ↝⁺ Y) → (xs : ⟦ D ⟧ X) (ys : ⟦ D ⟧ Y) → mapR D R xs ys → mapR D (R º⁺) ys xs
mapR-preserves-conv ∎       R xs         ys rs                           = tt
mapR-preserves-conv (ṿ i)   R x          y  r                            = r
mapR-preserves-conv (σ S D) R (s , xs)   ._ (ys , rs , refl)             = xs , mapR-preserves-conv (D s) R xs ys rs , refl
mapR-preserves-conv (D * E) R (xs , xs') ._ (ys , rs , ys' , rs' , refl) = xs  , mapR-preserves-conv D R xs  ys  rs  ,
                                                                           xs' , mapR-preserves-conv E R xs' ys' rs' , refl

mapR-fun-computation : {I : Set} (D : RDesc I) {X Y : I → Set} (f : X ⇒ Y) → (xs : ⟦ D ⟧ X) → mapR D (fun⁺ f) xs (mapF D f xs)
mapR-fun-computation ∎ f xs               = tt
mapR-fun-computation (ṿ i) f x            = refl
mapR-fun-computation (σ S D) f (s , xs)   = mapF (D s) f xs , mapR-fun-computation (D s) f xs , refl
mapR-fun-computation (D * E) f (xs , xs') = mapF D f xs , mapR-fun-computation D f xs , mapF E f xs' , mapR-fun-computation E f xs' , refl

mapR-fun-unique : {I : Set} (D : RDesc I) {X Y : I → Set} (f : X ⇒ Y) → (xs : ⟦ D ⟧ X) (ys : ⟦ D ⟧ Y) → mapR D (fun⁺ f) xs ys → mapF D f xs ≡ ys
mapR-fun-unique ∎       f xs         ys         r                            = refl
mapR-fun-unique (ṿ i)   f x          y          r                            = r
mapR-fun-unique (σ S D) f (s , xs)   (.s , ys)  (.ys , r , refl)             = cong (_,_ s) (mapR-fun-unique (D s) f xs ys r)
mapR-fun-unique (D * E) f (xs , xs') (ys , ys') (.ys , r , .ys' , r' , refl) = cong₂ _,_ (mapR-fun-unique D f xs ys r)
                                                                                         (mapR-fun-unique E f xs' ys' r')


--------
-- relators

Ṙ : {I : Set} (D : Desc I) {X Y : I → Set} → (X ↝⁺ Y) → Ḟ D X ↝⁺ Ḟ D Y
Ṙ D R i = mapR (D at i) R

Ṙ-monotonic : {I : Set} (D : Desc I) {X Y : I → Set} {R S : X ↝⁺ Y} → R ⊆⁺ S → Ṙ D R ⊆⁺ Ṙ D S
Ṙ-monotonic D R⊆⁺S i = mapR-monotonic (D at i) R⊆⁺S

Ṙ-cong : {I : Set} (D : Desc I) {X Y : I → Set} {R S : X ↝⁺ Y} → R ≃⁺ S → Ṙ D R ≃⁺ Ṙ D S
Ṙ-cong D R≃⁺S i = Ṙ-monotonic D (proj₁ ∘ R≃⁺S) i , Ṙ-monotonic D (proj₂ ∘ R≃⁺S) i

Ṙ-preserves-comp : {I : Set} (D : Desc I) {X Y Z : I → Set} (R : Y ↝⁺ Z) (S : X ↝⁺ Y) → Ṙ D (R •⁺ S) ≃⁺ Ṙ D R •⁺ Ṙ D S
Ṙ-preserves-comp D R S i = mapR-preserves-comp-⊆ (D at i) R S , mapR-preserves-comp-⊇ (D at i) R S

Ṙ-preserves-conv : {I : Set} (D : Desc I) {X Y : I → Set} (R : X ↝⁺ Y) → Ṙ D (R º⁺) ≃⁺ Ṙ D R º⁺
Ṙ-preserves-conv D R i = wrap (λ ys xs → mapR-preserves-conv (D at i) (R º⁺) ys xs) ,
                         wrap (λ ys xs → mapR-preserves-conv (D at i)  R     xs ys)

fun-preserves-map : {I : Set} (D : Desc I) {X Y : I → Set} (f : X ⇒ Y) → fun⁺ (Ḟ-map D (λ {i} → f {i})) ≃⁺ Ṙ D (fun⁺ f)
fun-preserves-map D f i = wrap (λ { xs ._ refl → mapR-fun-computation (D at i) f xs }) ,
                          wrap (λ xs → mapR-fun-unique (D at i) f xs)
