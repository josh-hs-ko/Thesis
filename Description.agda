-- Definition of datatype descriptions, i.e., a universe for functors on families of sets.
-- Datatype-generic fold and induction are defined on top of descriptions.

module Description where

open import Prelude.Category.Isomorphism
open import Prelude.Function
open import Prelude.Function.Fam
open import Prelude.Product

open import Function using (id; flip; _∘_)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; Σ-syntax; _,_; proj₁; _×_)
open import Data.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)


data RDesc (I : Set) : Set₁ where
  ṿ   : (is : List I) → RDesc I
  σ   : (S : Set) (D : S → RDesc I) → RDesc I

syntax σ S (λ s → D) = σ[ s ∈ S ] D

Ḣ : {I : Set} → RDesc I → (List I → Set) → Set
Ḣ (ṿ is)  X = X is
Ḣ (σ S D) X = Σ[ s ∈ S ] Ḣ (D s) X

Ṗ : {I : Set} → List I → (I → Set) → Set
Ṗ []       X = ⊤
Ṗ (i ∷ is) X = X i × Ṗ is X

generate-Ṗ : {I : Set} {X : I → Set} → ((i : I) → X i) → (is : List I) → Ṗ is X
generate-Ṗ f []       = tt
generate-Ṗ f (i ∷ is) = f i , generate-Ṗ f is

⟦_⟧ : {I : Set} → RDesc I → (I → Set) → Set
⟦ D ⟧ X = Ḣ D (flip Ṗ X)

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
  mapFold D (ṿ is)   f ds         = mapFold-Ṗ D f is ds
  mapFold D (σ S D') f (s , ds)   = s , mapFold D (D' s) f ds

  mapFold-Ṗ : {I : Set} (D : Desc I) {X : I → Set} → (Ḟ D X ⇉ X) → (is : List I) → Ṗ is (μ D) → Ṗ is X
  mapFold-Ṗ D f []       _        = tt
  mapFold-Ṗ D f (i ∷ is) (d , ds) = fold f d , mapFold-Ṗ D f is ds

-- induction

All-Ṗ : {I : Set} {X : I → Set} (P : (i : I) → X i → Set) → (is : List I) → Ṗ is X → Set
All-Ṗ P []       _        = ⊤
All-Ṗ P (i ∷ is) (x , xs) = P i x × All-Ṗ P is xs

All : {I : Set} (D : RDesc I) {X : I → Set} (P : (i : I) → X i → Set) → ⟦ D ⟧ X → Set
All (ṿ is)  P xs         = All-Ṗ P is xs
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
  everywhereInduction D (ṿ is)   P ih ds        = everywhereInduction-Ṗ D P ih is ds
  everywhereInduction D (σ S D') P ih (s , ds)  = everywhereInduction D (D' s) P ih ds

  everywhereInduction-Ṗ :
    {I : Set} (D : Desc I) (P : (i : I) → μ D i → Set) →
    ((i : I) (ds : Ḟ D (μ D) i) → All (Desc.comp D i) P ds → P i (con ds)) →
    (is : List I) (ds : Ṗ is (μ D)) → All-Ṗ P is ds
  everywhereInduction-Ṗ D P ih []       _        = tt
  everywhereInduction-Ṗ D P ih (i ∷ is) (d , ds) = induction D P ih d , everywhereInduction-Ṗ D P ih is ds

reflection : {I : Set} (D : Desc I) → ∀ {i} (x : μ D i) → fold con x ≡ x
reflection {I} D = induction D (λ _ x → fold con x ≡ x) (λ i xs all → cong con (aux (Desc.comp D i) xs all))
  where
    aux : (D' : RDesc I) (xs : ⟦ D' ⟧ (μ D)) → All D' (λ _ x → fold {D = D} con x ≡ x) xs → mapFold D D' con xs ≡ xs
    aux (ṿ [])       _          _          = refl
    aux (ṿ (i ∷ is)) (x , xs)   (ih , ihs) = cong₂ _,_ ih (aux (ṿ is) xs ihs)
    aux (σ S D')     (s , xs)   ihs        = cong (_,_ s) (aux (D' s) xs ihs)

-- maps

Ṗ-map : {I : Set} {X Y : I → Set} → (X ⇉ Y) → (is : List I) → Ṗ is X → Ṗ is Y
Ṗ-map f []       _        = tt
Ṗ-map f (i ∷ is) (x , xs) = f x , Ṗ-map f is xs

Ṗ-comp : {I : Set} {X Y : I → Set} (is : List I) → Ṗ is X → Ṗ is Y → Ṗ is (X ×' Y)
Ṗ-comp []       _        _        = tt
Ṗ-comp (i ∷ is) (x , xs) (y , ys) = (x , y) , Ṗ-comp is xs ys

Ḣ-map : {I : Set} (D : RDesc I) {X Y : List I → Set} → (X ⇉ Y) → Ḣ D X → Ḣ D Y
Ḣ-map (ṿ is)  f x        = f x
Ḣ-map (σ S D) f (s , xs) = s , Ḣ-map (D s) f xs

Ḣ-map-preserves-id : {I : Set} (D : RDesc I) {X : List I → Set} → Ḣ-map D {X} id ≐ id
Ḣ-map-preserves-id (ṿ is)       _        = refl
Ḣ-map-preserves-id (σ S D)      (s , xs) = cong (_,_ s) (Ḣ-map-preserves-id (D s) xs)

Ḣ-map-preserves-comp : {I : Set} (D : RDesc I) {X Y Z : List I → Set} (f : Y ⇉ Z) (g : X ⇉ Y) →
                       Ḣ-map D (λ {is} → f {is} ∘ g {is}) ≐ Ḣ-map D f ∘ Ḣ-map D g
Ḣ-map-preserves-comp (ṿ is)  f g xs       = refl
Ḣ-map-preserves-comp (σ S D) f g (s , xs) = cong (_,_ s) (Ḣ-map-preserves-comp (D s) f g xs)

mapF : {I : Set} (D : RDesc I) {X Y : I → Set} → (X ⇉ Y) → ⟦ D ⟧ X → ⟦ D ⟧ Y
mapF D f = Ḣ-map D (λ {is} → Ṗ-map f is)

mapF-preserves-id : {I : Set} (D : RDesc I) {X : I → Set} → mapF D (λ {i} → id {A = X i}) ≐ id
mapF-preserves-id (ṿ [])       _        = refl
mapF-preserves-id (ṿ (i ∷ is)) (x , xs) = cong (_,_ x) (mapF-preserves-id (ṿ is) xs)
mapF-preserves-id (σ S D)      (s , xs) = cong (_,_ s) (mapF-preserves-id (D s) xs)

mapF-preserves-comp : {I : Set} (D : RDesc I) {X Y Z : I → Set} (f : Y ⇉ Z) (g : X ⇉ Y) →
                      mapF D (λ {i} → f {i} ∘ g {i}) ≐ mapF D f ∘ mapF D g
mapF-preserves-comp (ṿ [])       f g _        = refl
mapF-preserves-comp (ṿ (i ∷ is)) f g (x , xs) = cong (_,_ (f (g x))) (mapF-preserves-comp (ṿ is) f g xs)
mapF-preserves-comp (σ S D)      f g (s , xs) = cong (_,_ s) (mapF-preserves-comp (D s) f g xs)

mapF-preserves-eq : {I : Set} (D : RDesc I) {X Y : I → Set} (f g : X ⇉ Y) → ({i : I} → f {i} ≐ g {i}) → mapF D (λ {i} → f {i}) ≐ mapF D g
mapF-preserves-eq (ṿ [])       f g fgeq _        = refl
mapF-preserves-eq (ṿ (i ∷ is)) f g fgeq (x , xs) = cong₂ _,_ (fgeq x) (mapF-preserves-eq (ṿ is) f g fgeq xs)
mapF-preserves-eq (σ S D)      f g fgeq (s , xs) = cong (_,_ s) (mapF-preserves-eq (D s) f g fgeq xs)

Ḟ-map : {I : Set} (D : Desc I) {X Y : I → Set} → (X ⇉ Y) → Ḟ D X ⇉ Ḟ D Y
Ḟ-map D f {i} = mapF (Desc.comp D i) f

Ḟ-map-preserves-id : {I : Set} (D : Desc I) {X : I → Set} → (i : I) → Ḟ-map D (λ {i} → id {A = X i}) {i} ≐ id
Ḟ-map-preserves-id D i = mapF-preserves-id (Desc.comp D i)

Ḟ-map-preserves-comp : {I : Set} (D : Desc I) {X Y Z : I → Set} (f : Y ⇉ Z) (g : X ⇉ Y) →
                       (i : I) → Ḟ-map D (λ {i} → f {i} ∘ g {i}) {i} ≐ Ḟ-map D f ∘ Ḟ-map D g
Ḟ-map-preserves-comp D f g i = mapF-preserves-comp (Desc.comp D i) f g

Ḟ-map-preserves-eq : {I : Set} (D : Desc I) {X Y : I → Set} (f g : X ⇉ Y) → ({i : I} → f {i} ≐ g {i}) →
                     (i : I) → Ḟ-map D (λ {i} → f {i}) {i} ≐ Ḟ-map D g
Ḟ-map-preserves-eq D f g fgeq i = mapF-preserves-eq (Desc.comp D i) f g fgeq
