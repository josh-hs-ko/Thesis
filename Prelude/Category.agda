module Thesis.Prelude.Category where

open import Thesis.Prelude.Equality

open import Level
open import Function using (_∘_)
open import Data.Product using (Σ; _,_; _×_)
open import Relation.Binary using (Setoid)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)


record Category {ℓ₀ ℓ₁ ℓ₂ : Level} : Set (suc (ℓ₀ ⊔ ℓ₁ ⊔ ℓ₂)) where
  infix 1 _==>_
  infix 1 _≈_
  infixr 5 _·_
  field
    Object   : Set ℓ₀
    Morphism : Object → Object → Setoid ℓ₁ ℓ₂
  _==>_ : Object → Object → Set ℓ₁
  _==>_ X Y = Setoid.Carrier (Morphism X Y)
  _≈_ : ∀ {X Y} → (X ==> Y) → (X ==> Y) → Set ℓ₂
  _≈_ {X} {Y} = Setoid._≈_ (Morphism X Y)
  field
    _·_ : ∀ {X Y Z} → Y ==> Z → X ==> Y → X ==> Z
    id  : ∀ {X} → X ==> X
    id-l   : ∀ {X Y} (f : X ==> Y) → (id · f) ≈ f
    id-r   : ∀ {X Y} (f : X ==> Y) → (f · id) ≈ f
    assoc  : ∀ {X Y Z W} (f : Z ==> W) (g : Y ==> Z) (h : X ==> Y) → ((f · g) · h) ≈ (f · (g · h))
    cong-l : ∀ {X Y Z} {f g : X ==> Y} (h : Y ==> Z) → f ≈ g → (h · f) ≈ (h · g)
    cong-r : ∀ {X Y Z} {f g : Y ==> Z} (h : X ==> Y) → f ≈ g → (f · h) ≈ (g · h)

Terminal : {ℓ₀ ℓ₁ ℓ₂ : Level} (C : Category {ℓ₀} {ℓ₁} {ℓ₂}) → Category.Object C → Set (ℓ₀ ⊔ ℓ₁ ⊔ ℓ₂)
Terminal C X = (Y : Object) → Σ[ f ∶ (Y ==> X) ] Unique (Morphism Y X) f
  where open Category C

record Functor {ℓ₀ ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ : Level} (C : Category {ℓ₀} {ℓ₁} {ℓ₂}) (D : Category {ℓ₃} {ℓ₄} {ℓ₅}) : Set (ℓ₀ ⊔ ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄ ⊔ ℓ₅) where
  open Category C using () renaming (Object to CObject; _==>_ to _=C=>_; _·_ to _·C_; _≈_ to _≈C_; id to idC)
  open Category D using () renaming (Object to DObject; _==>_ to _=D=>_; _·_ to _·D_; _≈_ to _≈D_; id to idD)
  field
    object   : CObject → DObject
    morphism : ∀ {X Y} → X =C=> Y → object X =D=> object Y
    ≈-respecting    : ∀ {X Y} {f g : X =C=> Y} → f ≈C g → morphism f ≈D morphism g
    id-preserving   : ∀ {X} → morphism (idC {X}) ≈D idD
    comp-preserving : ∀ {X Y Z} (f : Y =C=> Z) (g : X =C=> Y) → morphism (f ·C g) ≈D (morphism f ·D morphism g)

idF : {ℓ₀ ℓ₁ ℓ₂ : Level} (C : Category {ℓ₀} {ℓ₁} {ℓ₂}) → Functor C C
idF C = record { object   = Function.id
               ; morphism = Function.id
               ; ≈-respecting    = Function.id
               ; id-preserving   = λ {X} → Setoid.refl (Category.Morphism C X X)
               ; comp-preserving = λ {X} {Y} {Z} f g → Setoid.refl (Category.Morphism C X Z) }

_⋆_ : {ℓ₀ ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ ℓ₆ ℓ₇ ℓ₈ : Level}
      {C : Category {ℓ₀} {ℓ₁} {ℓ₂}} {D : Category {ℓ₃} {ℓ₄} {ℓ₅}} {E : Category {ℓ₆} {ℓ₇} {ℓ₈}} →
      Functor D E → Functor C D → Functor C E
_⋆_ {C = C} {D} {E} F G =
  record { object   = object F ∘ object G
         ; morphism = morphism F ∘ morphism G
         ; ≈-respecting    = ≈-respecting F ∘ ≈-respecting G
         ; id-preserving   =
             λ {X} → Setoid.trans (Morphism E (object F (object G X)) (object F (object G X))) 
                                  (≈-respecting F (id-preserving G)) (id-preserving F)
         ; comp-preserving =
             λ {X} {Y} {Z} f g → Setoid.trans (Morphism E (object F (object G X)) (object F (object G Z)))
                                              (≈-respecting F (comp-preserving G f g)) (comp-preserving F (morphism G f) (morphism G g)) }
  where open Category
        open Functor

record NatTrans {ℓ₀ ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ : Level} {C : Category {ℓ₀} {ℓ₁} {ℓ₂}} {D : Category {ℓ₃} {ℓ₄} {ℓ₅}}
                (F G : Functor C D) : Set (ℓ₀ ⊔ ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄ ⊔ ℓ₅) where
  open Category
  open Category C using () renaming (_==>_ to _=C=>_)
  open Category D using () renaming (_==>_ to _=D=>_; _≈_ to _≈D_; _·_ to _·D_)
  open Functor
  field
    comp : (X : Object C) → object F X =D=> object G X
    naturality : {X Y : Object C} (f : X =C=> Y) →  morphism G f ·D comp X ≈D comp Y ·D morphism F f

Funct : {ℓ₀ ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ : Level} (C : Category {ℓ₀} {ℓ₁} {ℓ₂}) (D : Category {ℓ₃} {ℓ₄} {ℓ₅}) → Category
Funct C D =
  record { Object   = Functor C D
         ; Morphism =
             λ F G → record { Carrier = NatTrans F G
                            ; _≈_ = λ t u → (X : Object C) → NatTrans.comp t X ≈D NatTrans.comp u X
                            ; isEquivalence =
                                record { refl  = λ X → Setoid.refl (Morphism D (object F X) (object G X))
                                       ; sym   = λ eqs X → Setoid.sym (Morphism D (object F X) (object G X)) (eqs X)
                                       ; trans = λ eqs eqs' X → Setoid.trans (Morphism D (object F X) (object G X)) (eqs X) (eqs' X) } }
         ; _·_ = λ t u → record { comp = λ X → NatTrans.comp t X ·D NatTrans.comp u X; naturality = {!!} }
         ; id  = {!!}
         ; id-l   = {!!}
         ; id-r   = {!!}
         ; assoc  = {!!}
         ; cong-l = {!!}
         ; cong-r = {!!} }
  where open Category
        open Category D using () renaming (_≈_ to _≈D_;_·_ to _·D_)
        open Functor