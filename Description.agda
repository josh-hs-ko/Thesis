-- Definition of datatype descriptions, i.e., a universe for functors on families of sets.
-- Datatype-generic fold and induction are defined on top of descriptions.

module Thesis.Description where

open import Thesis.Prelude.Category.Isomorphism
open import Thesis.Prelude.Function
open import Thesis.Prelude.Function.Fam
open import Thesis.Prelude.Product

open import Function using (id)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; _×_)
open import Data.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)


data RDesc (I : Set) : Set₁ where
  ṿ   : (is : List I) → RDesc I
  σ   : (S : Set) (D : S → RDesc I) → RDesc I

syntax σ S (λ s → D) = σ[ s ∶ S ] D

Ḣ : {I : Set} → RDesc I → (List I → Set) → Set
Ḣ (ṿ is)  X = X is
Ḣ (σ S D) X = Σ[ s ∶ S ] Ḣ (D s) X

Ṁ : {I : Set} → (I → Set) → List I → Set
Ṁ X []       = ⊤
Ṁ X (i ∷ is) = X i × Ṁ X is

generate-Ṁ : {I : Set} {X : I → Set} → ((i : I) → X i) → (is : List I) → Ṁ X is
generate-Ṁ f []       = tt
generate-Ṁ f (i ∷ is) = f i , generate-Ṁ f is

⟦_⟧ : {I : Set} → RDesc I → (I → Set) → Set
⟦ D ⟧ X = Ḣ D (Ṁ X)

record Desc (I : Set) : Set₁ where
  constructor wrap
  field
    comp : I → RDesc I

Ḟ : {I : Set} → Desc I → (I → Set) → (I → Set)
Ḟ D X i = ⟦ Desc.comp D i ⟧ X

data μ {I : Set} (D : Desc I) : I → Set where
  con : Ḟ D (μ D) ⇉ μ D

decon : {I : Set} {D : Desc I} → μ D ⇉ Ḟ D (μ D)
decon (con xs) = xs

μ-iso : {I : Set} (D : Desc I) → (i : I) → Iso Fun (μ D i) (Ḟ D (μ D) i)
μ-iso D i = record { to   = decon
                   ; from = con
                   ; to-from-inverse = frefl
                   ; from-to-inverse = λ { (con xs) → refl } }

-- fold

mutual

  fold : {I : Set} {D : Desc I} {X : I → Set} → Ḟ D X ⇉ X → μ D ⇉ X
  fold {D = D} f {i} (con ds) = f (mapFold D (Desc.comp D i) f ds)

  mapFold : {I : Set} (D : Desc I) (D' : RDesc I) → {X : I → Set} → (Ḟ D X ⇉ X) → ⟦ D' ⟧ (μ D) → ⟦ D' ⟧ X
  mapFold D (ṿ is)   f ds         = mapFold-Ṁ D f is ds
  mapFold D (σ S D') f (s , ds)   = s , mapFold D (D' s) f ds

  mapFold-Ṁ : {I : Set} (D : Desc I) {X : I → Set} → (Ḟ D X ⇉ X) → (is : List I) → Ṁ (μ D) is → Ṁ X is
  mapFold-Ṁ D f []       _        = tt
  mapFold-Ṁ D f (i ∷ is) (d , ds) = fold f d , mapFold-Ṁ D f is ds

-- induction

All-Ṁ : {I : Set} {X : I → Set} (P : (i : I) → X i → Set) → (is : List I) → Ṁ X is → Set
All-Ṁ P []       _        = ⊤
All-Ṁ P (i ∷ is) (x , xs) = P i x × All-Ṁ P is xs

All : {I : Set} (D : RDesc I) {X : I → Set} (P : (i : I) → X i → Set) → ⟦ D ⟧ X → Set
All (ṿ is)  P xs         = All-Ṁ P is xs
All (σ S D) P (s , xs)   = All (D s) P xs

mutual

  induction : {I : Set} (D : Desc I) (P : (i : I) → μ D i → Set) →
              ((i : I) (ds : Ḟ D (μ D) i) → All (Desc.comp D i) P ds → P i (con ds)) →
              {i : I} (d : μ D i) → P i d
  induction D P ih {i} (con ds) = ih i ds (everywhereInduction D (Desc.comp D i) P ih ds)

  everywhereInduction :
    {I : Set} (D : Desc I) (D' : RDesc I)
    (P : (i : I) → μ D i → Set) →
    ((i : I) (ds : Ḟ D (μ D) i) → All (Desc.comp D i) P ds → P i (con ds)) →
    (ds : ⟦ D' ⟧ (μ D)) → All D' P ds
  everywhereInduction D (ṿ is)   P ih ds         = everywhereInduction-Ṁ D P ih is ds
  everywhereInduction D (σ S D') P ih (s , ds)   = everywhereInduction D (D' s) P ih ds

  everywhereInduction-Ṁ :
    {I : Set} (D : Desc I) (P : (i : I) → μ D i → Set) →
    ((i : I) (ds : Ḟ D (μ D) i) → All (Desc.comp D i) P ds → P i (con ds)) →
    (is : List I) (ds : Ṁ (μ D) is) → All-Ṁ P is ds
  everywhereInduction-Ṁ D P ih []       _        = tt
  everywhereInduction-Ṁ D P ih (i ∷ is) (d , ds) = induction D P ih d , everywhereInduction-Ṁ D P ih is ds

reflection : {I : Set} (D : Desc I) → ∀ {i} (x : μ D i) → fold con x ≡ x
reflection {I} D = induction D (λ _ x → fold con x ≡ x) (λ i xs all → cong con (aux (Desc.comp D i) xs all))
  where
    aux : (D' : RDesc I) (xs : ⟦ D' ⟧ (μ D)) → All D' (λ _ x → fold {D = D} con x ≡ x) xs → mapFold D D' con xs ≡ xs
    aux (ṿ [])       _          _          = refl
    aux (ṿ (i ∷ is)) (x , xs)   (ih , ihs) = cong₂ _,_ ih (aux (ṿ is) xs ihs)
    aux (σ S D')     (s , xs)   ihs        = cong (_,_ s) (aux (D' s) xs ihs)

-- maps

Ṁ-map : {I : Set} {X Y : I → Set} → (X ⇉ Y) → (is : List I) → Ṁ X is → Ṁ Y is
Ṁ-map f []       _        = tt
Ṁ-map f (i ∷ is) (x , xs) = f x , Ṁ-map f is xs

Ṁ-comp : {I : Set} {X Y : I → Set} (is : List I) → Ṁ X is → Ṁ Y is → Ṁ (X ×' Y) is
Ṁ-comp []       _        _        = tt
Ṁ-comp (i ∷ is) (x , xs) (y , ys) = (x , y) , Ṁ-comp is xs ys

Ḣ-map : {I : Set} (D : RDesc I) {X Y : List I → Set} → (X ⇉ Y) → Ḣ D X → Ḣ D Y
Ḣ-map (ṿ is)  f x        = f x
Ḣ-map (σ S D) f (s , xs) = s , Ḣ-map (D s) f xs

mapF : {I : Set} (D : RDesc I) {X Y : I → Set} → (X ⇉ Y) → ⟦ D ⟧ X → ⟦ D ⟧ Y
mapF D f = Ḣ-map D (λ {is} → Ṁ-map f is)

mapF-preserves-id : {I : Set} (D : RDesc I) {X : I → Set} → mapF D (λ {i} → id {A = X i}) ≐ id
mapF-preserves-id (ṿ [])       _        = refl
mapF-preserves-id (ṿ (i ∷ is)) (x , xs) = cong₂ _,_ refl (mapF-preserves-id (ṿ is) xs)
mapF-preserves-id (σ S D)      (s , xs) = cong (_,_ s) (mapF-preserves-id (D s) xs)

Ḟ-map : {I : Set} (D : Desc I) {X Y : I → Set} → (X ⇉ Y) → Ḟ D X ⇉ Ḟ D Y
Ḟ-map D f {i} = mapF (Desc.comp D i) f

Ḟ-map-preserves-id : {I : Set} (D : Desc I) {X : I → Set} → (i : I) → Ḟ-map D (λ {i} → id {A = X i}) {i} ≐ id
Ḟ-map-preserves-id D i = mapF-preserves-id (Desc.comp D i)
