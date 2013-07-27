-- Definition of datatype descriptions, i.e., a universe for functors on families of sets.
-- Datatype-generic fold and induction are defined on top of descriptions.

module Description where

open import Prelude.Category.Isomorphism
open import Prelude.Function
open import Prelude.Function.Fam

open import Function using (id; const)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)


data RDesc (I : Set) : Set₁ where
  ∎   : RDesc I
  ṿ   : (i : I) → RDesc I
  σ   : (S : Set) (D : S → RDesc I) → RDesc I
  _*_ : (D E : RDesc I) → RDesc I

syntax σ S (λ s → D) = σ[ s ∶ S ] D

⟦_⟧ : ∀ {I} → RDesc I → (I → Set) → Set
⟦ ∎     ⟧ X = ⊤
⟦ ṿ i   ⟧ X = X i
⟦ σ S D ⟧ X = Σ[ s ∶ S ] ⟦ D s ⟧ X
⟦ D * E ⟧ X = ⟦ D ⟧ X × ⟦ E ⟧ X

record Desc (I : Set) : Set₁ where
  constructor wrap
  field
    comp : I → RDesc I

_at_ : ∀ {I} → Desc I → I → RDesc I
(wrap D) at i = D i

Ḟ : ∀ {I} → Desc I → (I → Set) → (I → Set)
Ḟ D X i = ⟦ D at i ⟧ X

data μ {I} (D : Desc I) : I → Set where
  con : Ḟ D (μ D) ⇉ μ D

decon : ∀ {I} {D : Desc I} → μ D ⇉ Ḟ D (μ D)
decon (con xs) = xs

μ-iso : ∀ {I} (D : Desc I) → ∀ i → Iso Fun (μ D i) (Ḟ D (μ D) i)
μ-iso D i = record { to   = decon
                   ; from = con
                   ; to-from-inverse = frefl
                   ; from-to-inverse = λ { (con xs) → refl } }

-- fold

mutual

  fold : ∀ {I X} {D : Desc I} → Ḟ D X ⇉ X → μ D ⇉ X
  fold {D = D} φ {i} (con ds) = φ (mapFold D (D at i) φ ds)

  mapFold : ∀ {I} (D : Desc I) (E : RDesc I) → ∀ {X} → (Ḟ D X ⇉ X) → ⟦ E ⟧ (μ D) → ⟦ E ⟧ X
  mapFold D ∎        φ _          = _
  mapFold D (ṿ i)    φ d          = fold φ d
  mapFold D (σ S E)  φ (s , ds)   = s , mapFold D (E s) φ ds
  mapFold D (E * E') φ (ds , ds') = mapFold D E φ ds , mapFold D E' φ ds'

-- induction

All : ∀ {I} (D : RDesc I) {X : I → Set} (P : ∀ {i} → X i → Set) → ⟦ D ⟧ X → Set
All ∎       P _          = ⊤
All (ṿ i)   P x          = P x
All (σ S D) P (s , xs)   = All (D s) P xs
All (D * E) P (xs , xs') = All D P xs × All E P xs'

mutual

  induction : ∀ {I} (D : Desc I) (P : ∀ {i} → μ D i → Set) →
              (∀ {i} (ds : Ḟ D (μ D) i) → All (D at i) P ds → P (con ds)) →
              ∀ {i} (d : μ D i) → P d
  induction D P ih {i} (con ds) = ih ds (everywhereInduction D (D at i) P ih ds)

  everywhereInduction :
    ∀ {I} (D : Desc I) (E : RDesc I)
    (P : ∀ {i} → μ D i → Set) →
    (∀ {i} (ds : Ḟ D (μ D) i) → All (D at i) P ds → P (con ds)) →
    (ds : ⟦ E ⟧ (μ D)) → All E P ds
  everywhereInduction D ∎        P ih _          = _
  everywhereInduction D (ṿ i)    P ih d          = induction D P ih d
  everywhereInduction D (σ S E)  P ih (s , ds)   = everywhereInduction D (E s) P ih ds
  everywhereInduction D (E * E') P ih (ds , ds') = everywhereInduction D E P ih ds ,
                                                   everywhereInduction D E' P ih ds'

reflection : ∀ {I} (D : Desc I) → ∀ {i} (x : μ D i) → fold con x ≡ x
reflection {I} D = induction D (λ x → fold con x ≡ x) (λ {i} xs all → cong con (aux (D at i) xs all))
  where
    aux : (D' : RDesc I) (xs : ⟦ D' ⟧ (μ D)) (all : All D' (λ x → fold {D = D} con x ≡ x) xs) → mapFold D D' con xs ≡ xs
    aux ∎         xs         all          = refl
    aux (ṿ i)     xs         all          = all
    aux (σ S D')  (s , xs)   all          = cong (_,_ s) (aux (D' s) xs all)
    aux (D' * E') (xs , xs') (all , all') = cong₂ _,_ (aux D' xs all) (aux E' xs' all')

-- maps

mapF : ∀ {I} (D : RDesc I) {X Y} → (X ⇉ Y) → ⟦ D ⟧ X → ⟦ D ⟧ Y
mapF ∎       f xs         = tt
mapF (ṿ i)   f x          = f x
mapF (σ S D) f (s , xs)   = s , mapF (D s) f xs
mapF (D * E) f (xs , xs') = mapF D f xs , mapF E f xs'

mapF-preserves-id : ∀ {I} (D : RDesc I) {X : I → Set} → mapF D (λ {i} → id {A = X i}) ≐ id
mapF-preserves-id ∎ xs               = refl
mapF-preserves-id (ṿ i) x            = refl
mapF-preserves-id (σ S D) (s , xs)   = cong (_,_ s) (mapF-preserves-id (D s) xs)
mapF-preserves-id (D * E) (xs , xs') = cong₂ _,_ (mapF-preserves-id D xs) (mapF-preserves-id E xs')

remove-recursive-objects : ∀ {I} (D : RDesc I) {X} → ⟦ D ⟧ X → ⟦ D ⟧ (const ⊤)
remove-recursive-objects D = mapF D !

Ḟ-map : ∀ {I} (D : Desc I) {X Y} → (X ⇉ Y) → Ḟ D X ⇉ Ḟ D Y
Ḟ-map D f {i} = mapF (D at i) f

Ḟ-map-preserves-id : ∀ {I} (D : Desc I) {X : I → Set} → ∀ i → Ḟ-map D (λ {i} → id {A = X i}) {i} ≐ id
Ḟ-map-preserves-id D i = mapF-preserves-id (D at i)
