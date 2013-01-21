module Thesis.Relation where

open import Thesis.Prelude.Category.Isomorphism
open import Thesis.Prelude.Function
open import Thesis.Prelude.Function.Fam
open import Thesis.Description

open import Function using (id; _∘_; flip; type-signature)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; _×_)
open import Relation.Binary using (Setoid; Preorder)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans) renaming (setoid to ≡-Setoid)


--------
-- subsets

℘ : Set → Set₁
℘ A = A → Set

return : ∀ {A} → A → ℘ A
return = _≡_

_>>=_ : ∀ {A B} → (S : ℘ A) → (A → ℘ B) → ℘ B
_>>=_ {A} S f = λ y → Σ[ x ∶ A ] S x × f x y

map℘ : ∀ {A B} → (A → B) → ℘ A → ℘ B
map℘ f s = s >>= (return ∘ f)

map℘₂ : ∀ {A B C} → (A → B → C) → ℘ A → ℘ B → ℘ C
map℘₂ f s t = s >>= λ x → t >>= λ y → return (f x y)

-- ∀ y. (return x >>= f) y ⇔ f x y
-- ∀ y. (s >>= return) y ⇔ s y

any : ∀ {A} → ℘ A
any _ = ⊤

any>>=_ : ∀ {A B} → (A → ℘ B) → ℘ B
any>>=_ {A} f = λ y → Σ[ x ∶ A ] f x y

infix 2 any>>=_

none : ∀ {A} → ℘ A
none _ = ⊥


--------
-- relations

record _↝_ {I : Set} (X Y : I → Set) : Set₁ where
  constructor wrap
  field
    comp : ∀ {i} → X i → ℘ (Y i)

Λ : ∀ {I} {X Y : I → Set} → (X ↝ Y) → ∀ {i} → X i → ℘ (Y i)
Λ = _↝_.comp

fun : ∀ {I} {X Y : I → Set} → (X ⇒ Y) → X ↝ Y
fun f = wrap (return ∘ f)

idR : ∀ {I} {X : I → Set} → X ↝ X
idR = fun id

α : ∀ {I} {D : Desc I} → Ḟ D (μ D) ↝ μ D
α = fun con

infix 6 _º

_º : ∀ {I} {X Y : I → Set} → (X ↝ Y) → Y ↝ X
(wrap R) º = wrap (flip R)

infixr 4 _•_

_•_ : ∀ {I} {X Y Z : I → Set} → (Y ↝ Z) → (X ↝ Y) → X ↝ Z
_•_ R S = wrap λ x → Λ S x >>= Λ R


--------
-- relational fold

mutual

  foldR' : ∀ {I} {D : Desc I} {X} → (Ḟ D X ↝ X) → ∀ {i} → μ D i → ℘ (X i)
  foldR' {I} {D} {X} R {i} (con ds) = mapFoldR D (D at i) R ds >>= Λ R

  mapFoldR : ∀ {I} (D : Desc I) (E : RDesc I) → ∀ {X} → (Ḟ D X ↝ X) → ⟦ E ⟧ (μ D) → ℘ (⟦ E ⟧ X)
  mapFoldR D ∎        R _          = any
  mapFoldR D (ṿ i)    R d          = foldR' R d
  mapFoldR D (σ S E)  R (s , ds)   = map℘ (_,_ s) (mapFoldR D (E s) R ds)
  mapFoldR D (E * E') R (ds , ds') = map℘₂ _,_ (mapFoldR D E R ds) (mapFoldR D E' R ds')

foldR : ∀ {I} {D : Desc I} {X} → (Ḟ D X ↝ X) → μ D ↝ X
foldR R = wrap (foldR' R)


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

record _⊆_ {I : Set} {X Y : I → Set} (R S : X ↝ Y) : Set where
  constructor wrap
  field
    comp : ∀ {i} (x : X i) → Λ R x ⊑ Λ S x

modus-ponens-⊆ : {I : Set} {X Y : I → Set} {R S : X ↝ Y} → R ⊆ S → ∀ {i} (x : X i) (y : Y i) → Λ R x y → Λ S x y
modus-ponens-⊆ (wrap R⊆S) = modus-ponens-⊑ ∘ R⊆S

infix 3 _⊇_

_⊇_ : {I : Set} {X Y : I → Set} → (X ↝ Y) → (X ↝ Y) → Set
R ⊇ S = S ⊆ R

⊆-refl : {I : Set} {X Y : I → Set} {R : X ↝ Y} → R ⊆ R
⊆-refl = wrap λ _ → ⊑-refl

⊆-trans : {I : Set} {X Y : I → Set} {R S T : X ↝ Y} → R ⊆ S → S ⊆ T → R ⊆ T
⊆-trans (wrap R⊆S) (wrap S⊆T) = wrap λ x → ⊑-trans (R⊆S x) (S⊆T x)

⊆-Preorder : {I : Set} (X Y : I → Set) → Preorder _ _ _
⊆-Preorder X Y =
  record { Carrier = X ↝ Y
         ; _≈_ = _≡_
         ; _∼_ = _⊆_
         ; isPreorder =
             record { isEquivalence = Setoid.isEquivalence (≡-Setoid _)
                    ; reflexive     = λ { {._} refl → ⊆-refl }
                    ; trans         = ⊆-trans } }

º-monotonic : {I : Set} {X Y : I → Set} {R S : X ↝ Y} → R ⊆ S → R º ⊆ S º
º-monotonic R⊆S = wrap λ y → wrap λ x r → modus-ponens-⊆ R⊆S x y r

•-monotonic-l : {I : Set} {X Y Z : I → Set} {R S : X ↝ Y} (T : Y ↝ Z) → R ⊆ S → T • R ⊆ T • S
•-monotonic-l T R⊆S = wrap λ x → wrap λ { z (y , r , t) → y , modus-ponens-⊆ R⊆S x y r , t }

•-monotonic-r : {I : Set} {X Y Z : I → Set} {R S : X ↝ Y} (T : Z ↝ X) → R ⊆ S → R • T ⊆ S • T
•-monotonic-r T R⊆S = wrap λ z → wrap λ { y (x , t , r) → x , t , modus-ponens-⊆ R⊆S x y r }


--------
-- relational bi-inclusion

infix 3 _≃_

_≃_ : {I : Set} {X Y : I → Set} → (X ↝ Y) → (X ↝ Y) → Set
R ≃ S = (R ⊆ S) × (R ⊇ S)

≃-Setoid : {I : Set} (X Y : I → Set) → Setoid _ _
≃-Setoid {I} X Y =
  record { Carrier = X ↝ Y
         ; _≈_ = _≃_
         ; isEquivalence =
             record { refl  = ⊆-refl , ⊆-refl
                    ; sym   = λ { (p , q) → q , p }
                    ; trans = λ { (R⊆S , S⊆R) (S⊆T , T⊆S) → ⊆-trans R⊆S S⊆T , ⊆-trans T⊆S S⊆R } } }

iso-conv : {I : Set} {X Y : I → Set} → (iso : ∀ i → Iso Fun (X i) (Y i)) →
               fun (λ {i} → Iso.to Fun (iso i)) º ≃ fun (λ {i} → Iso.from Fun (iso i))
iso-conv iso =
  (wrap (λ {i} y → wrap (λ x eq → trans (sym (cong (from (iso i)) eq)) (from-to-inverse (iso i) x)))) ,
  (wrap (λ {i} y → wrap (λ x eq → trans (sym (cong (to   (iso i)) eq)) (to-from-inverse (iso i) y))))
  where open Iso Fun

fun-preserves-comp : {I : Set} {X Y Z : I → Set} (f : Y ⇒ Z) (g : X ⇒ Y) → fun (λ {i} → f {i} ∘ g) ≃ fun f • fun g
fun-preserves-comp f g = wrap (λ x → wrap λ { ._ refl → g x , refl , refl }) , wrap (λ x → wrap λ { ._ (._ , refl , refl) → refl })

º-preserves-comp : {I : Set} {X Y Z : I → Set} (R : Y ↝ Z) (S : X ↝ Y) → (R • S)º ≃ S º • R º
º-preserves-comp R S = wrap (λ z → wrap λ { x (y , s , r) → y , r , s }) , wrap (λ z → wrap (λ { x (y , r , s) → y , s , r }))

fun-cong : {I : Set} {X Y : I → Set} {f g : X ⇒ Y} → (∀ {i} → f {i} ≐ g {i}) → fun {X = X} {Y} f ≃ fun g
fun-cong f≐g = wrap (λ x → wrap λ { ._ refl → fsym f≐g x }) , wrap (λ x → wrap λ { ._ refl → f≐g x })

º-cong : {I : Set} {X Y : I → Set} {R S : X ↝ Y} → R ≃ S → R º ≃ S º
º-cong (R⊆S , R⊇S) = º-monotonic R⊆S , º-monotonic R⊇S

idR-l : {I : Set} {X Y : I → Set} (R : X ↝ Y) → idR • R ≃ R
idR-l R = (wrap λ x → wrap λ { y (.y , r , refl) → r }) , wrap (λ x → wrap λ y r → y , r , refl)

idR-r : {I : Set} {X Y : I → Set} (R : X ↝ Y) → R • idR ≃ R
idR-r R = (wrap λ x → wrap λ { y (.x , refl , r) → r }) , wrap (λ x → wrap λ y r → x , refl , r)

•-cong-l : {I : Set} {X Y Z : I → Set} {R S : X ↝ Y} (T : Y ↝ Z) → R ≃ S → T • R ≃ T • S
•-cong-l T (R⊆S , R⊇S) = •-monotonic-l T R⊆S , •-monotonic-l T R⊇S

•-cong-r : {I : Set} {X Y Z : I → Set} {R S : X ↝ Y} (T : Z ↝ X) → R ≃ S → R • T ≃ S • T
•-cong-r T (R⊆S , R⊇S) = •-monotonic-r T R⊆S , •-monotonic-r T R⊇S

•-assoc : {I : Set} {X Y Z W : I → Set} (R : Z ↝ W) (S : Y ↝ Z) (T : X ↝ Y) → (R • S) • T ≃ R • (S • T)
•-assoc R S T = wrap (λ x → wrap λ { w (y , t , z , s , r) → z , (y , t , s) , r }) ,
                wrap (λ x → wrap λ { w (z , (y , t , s) , r) → y , t , z , s , r })


--------
-- functorial map

mapR : {I : Set} (D : RDesc I) {X Y : I → Set} → (X ↝ Y) → ⟦ D ⟧ X → ℘ (⟦ D ⟧ Y)
mapR ∎       R xs         = any
mapR (ṿ i)   R x          = Λ R x
mapR (σ S D) R (s , xs)   = map℘ (_,_ s) (mapR (D s) R xs)
mapR (D * E) R (xs , xs') = map℘₂ _,_ (mapR D R xs) (mapR E R xs')

mapR-monotonic : {I : Set} (D : RDesc I) {X Y : I → Set} {R S : X ↝ Y} → R ⊆ S → ∀ xs → mapR D R xs ⊑ mapR D S xs
mapR-monotonic ∎       R⊆S xs         = ⊑-refl
mapR-monotonic (ṿ i)   R⊆S x          = _⊆_.comp R⊆S x
mapR-monotonic (σ S D) R⊆S (s , xs)   = map℘-monotonic (_,_ s) (mapR-monotonic (D s) R⊆S xs)
mapR-monotonic (D * E) R⊆S (xs , xs') = map℘₂-monotonic _,_ (mapR-monotonic D R⊆S xs) (mapR-monotonic E R⊆S xs')

mapR-preserves-comp-⊑ :
  {I : Set} (D : RDesc I) {X Y Z : I → Set} (R : Y ↝ Z) (S : X ↝ Y) → ∀ xs → mapR D (R • S) xs ⊑ (mapR D S xs >>= mapR D R)
mapR-preserves-comp-⊑ ∎ R S xs = wrap λ _ _ → tt , tt , tt
mapR-preserves-comp-⊑ (ṿ i) R S x = ⊑-refl
mapR-preserves-comp-⊑ (σ T D) R S (t , xs) =
  ⊑-trans (map℘-monotonic (_,_ t) (mapR-preserves-comp-⊑ (D t) R S xs))
          (wrap (λ { (.t , zs) (.zs , (ys , s , r) , refl) → (t , ys) , (ys , (s , refl)) , (zs , r , refl) })
             ∶ (map℘ (_,_ t) (mapR (D t) S xs >>= mapR (D t) R) ⊑ mapR (σ T D) S (t , xs) >>= mapR (σ T D) R))
mapR-preserves-comp-⊑ (D * E) R S (xs , xs') =
  ⊑-trans (map℘₂-monotonic _,_ (mapR-preserves-comp-⊑ D R S xs) (mapR-preserves-comp-⊑ E R S xs'))
          (wrap (λ { (zs , zs') (.zs , (ys , s , r) , .zs' , (ys' , s' , r') , refl) →
                      (ys , ys') , (ys , s , ys' , s' , refl) , (zs , r , zs' , r' , refl) })
             ∶ (map℘₂ _,_ (mapR D S xs >>= mapR D R) (mapR E S xs' >>= mapR E R) ⊑ mapR (D * E) S (xs , xs') >>= mapR (D * E) R))

mapR-preserves-comp-⊒ :
  {I : Set} (D : RDesc I) {X Y Z : I → Set} (R : Y ↝ Z) (S : X ↝ Y) → ∀ xs → mapR D (R • S) xs ⊒ (mapR D S xs >>= mapR D R)
mapR-preserves-comp-⊒ ∎ R S xs = wrap λ _ _ → tt
mapR-preserves-comp-⊒ (ṿ i) R S x = ⊑-refl
mapR-preserves-comp-⊒ (σ T D) {X} {Y} {Z} R S (t , xs) =
  ⊑-trans (wrap (λ { (.t , zs) ((.t , ys) , (.ys , s , refl) , (.zs , r , refl)) → zs , (ys , s , r) , refl })
             ∶ mapR (σ T D) S (t , xs) >>= mapR (σ T D) R 
                ⊑ map℘ (_,_ t) (λ zs → Σ[ ys ∶ ⟦ D t ⟧ Y ] mapR (D t) S xs ys × mapR (D t) R ys zs))
          (map℘-monotonic (_,_ t) (mapR-preserves-comp-⊒ (D t) R S xs))
mapR-preserves-comp-⊒ (D * E) R S (xs , xs') =
  ⊑-trans (wrap (λ { (zs , zs') ((ys , ys') , (.ys , s , .ys' , s' , refl) , (.zs , r , .zs' , r' , refl)) →
                       zs , ((ys , s , r) , zs' , (ys' , s' , r') , refl) })
             ∶ mapR (D * E) S (xs , xs') >>= mapR (D * E) R
                ⊑ map℘₂ _,_ (mapR D S xs >>= mapR D R) (mapR E S xs' >>= mapR E R))
          (map℘₂-monotonic _,_ (mapR-preserves-comp-⊒ D R S xs) (mapR-preserves-comp-⊒ E R S xs'))

mapR-preserves-conv :
  {I : Set} (D : RDesc I) {X Y : I → Set} (R : X ↝ Y) (xs : ⟦ D ⟧ X) (ys : ⟦ D ⟧ Y) → mapR D R xs ys → mapR D (R º) ys xs
mapR-preserves-conv ∎       R xs         ys         rs                             = tt
mapR-preserves-conv (ṿ i)   R x          y          r                              = r
mapR-preserves-conv (σ S D) R (s , xs)   (.s , ys)  (.ys , rs , refl)              = xs , mapR-preserves-conv (D s) R xs ys rs , refl
mapR-preserves-conv (D * E) R (xs , xs') (ys , ys') (.ys , rs , .ys' , rs' , refl) =
  xs , mapR-preserves-conv D R xs ys rs , xs' , (mapR-preserves-conv E R xs' ys' rs' , refl)


--------
-- relators

Ṙ : {I : Set} (D : Desc I) {X Y : I → Set} → (X ↝ Y) → Ḟ D X ↝ Ḟ D Y
Ṙ D R = wrap λ {i} → mapR (D at i) R

Ṙ-monotonic : {I : Set} (D : Desc I) {X Y : I → Set} {R S : X ↝ Y} → R ⊆ S → Ṙ D R ⊆ Ṙ D S
Ṙ-monotonic D R⊆S = wrap λ {i} → mapR-monotonic (D at i) R⊆S

Ṙ-cong : {I : Set} (D : Desc I) {X Y : I → Set} {R S : X ↝ Y} → R ≃ S → Ṙ D R ≃ Ṙ D S
Ṙ-cong D (R⊆S , R⊇S) = Ṙ-monotonic D R⊆S , Ṙ-monotonic D R⊇S

Ṙ-preserves-conv : {I : Set} (D : Desc I) {X Y : I → Set} (R : X ↝ Y) → Ṙ D (R º) ≃ Ṙ D R º
Ṙ-preserves-conv D R = wrap (λ {i} ys → wrap λ xs → mapR-preserves-conv (D at i) (R º) ys xs) ,
                      wrap (λ {i} ys → wrap λ xs → mapR-preserves-conv (D at i) R     xs ys)

Ṙ-preserves-comp : {I : Set} (D : Desc I) {X Y Z : I → Set} (R : Y ↝ Z) (S : X ↝ Y) → Ṙ D (R • S) ≃ Ṙ D R • Ṙ D S
Ṙ-preserves-comp D R S = wrap (λ {i} → mapR-preserves-comp-⊑ (D at i) R S) , wrap (λ {i} → mapR-preserves-comp-⊒ (D at i) R S)