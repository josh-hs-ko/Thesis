-- An inductively defined equivalence between description-based data that poses little restriction on their actual types.

module Description.HorizontalEquivalence where

open import Description

open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)
open import Relation.Binary.HeterogeneousEquality using (_≅_; ≅-to-≡; ≡-to-≅) renaming (refl to hrefl; sym to hsym; trans to htrans)


data HoriEq {I : Set} {X Y : I → Set} : (D : RDesc I) → ⟦ D ⟧ X → (E : RDesc I) → ⟦ E ⟧ Y → Set₁ where
  ∎   : HoriEq ∎ tt ∎ tt
  ṿ   : {i : I} {x : X i} {y : Y i} → x ≅ y → HoriEq (ṿ i) x (ṿ i) y
  σ   : {S : Set} (s : S) → ∀ {D E xs ys} → HoriEq (D s) xs (E s) ys → HoriEq (σ S D) (s , xs) (σ S E) (s , ys)
  _*_ : ∀ {D E xs ys} → HoriEq D xs E ys → ∀ {D' E' xs' ys'} → HoriEq D' xs' E' ys' → HoriEq (D * D') (xs , xs') (E * E') (ys , ys')

HoriEq-refl : ∀ {I} {D : RDesc I} {X : I → Set} {xs : ⟦ D ⟧ X} → HoriEq D xs D xs
HoriEq-refl {D = ∎    } {xs = xs      } = ∎
HoriEq-refl {D = ṿ i  } {xs = xs      } = ṿ hrefl
HoriEq-refl {D = σ S D} {xs = s , xs  } = σ s HoriEq-refl
HoriEq-refl {D = D * E} {xs = xs , xs'} = HoriEq-refl * HoriEq-refl

HoriEq-sym : ∀ {I} {D E : RDesc I} {X Y : I → Set} {xs : ⟦ D ⟧ X} {ys : ⟦ E ⟧ Y} → HoriEq D xs E ys → HoriEq E ys D xs
HoriEq-sym ∎            = ∎
HoriEq-sym (ṿ heq)      = ṿ (hsym heq)
HoriEq-sym (σ s heq)    = σ s (HoriEq-sym heq)
HoriEq-sym (heq * heq') = HoriEq-sym heq * HoriEq-sym heq'

HoriEq-trans : ∀ {I} {D E F : RDesc I} {X Y Z : I → Set} {xs : ⟦ D ⟧ X} {ys : ⟦ E ⟧ Y} {zs : ⟦ F ⟧ Z} →
               HoriEq D xs E ys → HoriEq E ys F zs → HoriEq D xs F zs
HoriEq-trans ∎            ∎                = ∎
HoriEq-trans (ṿ heq)      (ṿ heq')         = ṿ (htrans heq heq')
HoriEq-trans (σ s heq)    (σ .s heq')      = σ s (HoriEq-trans heq heq')
HoriEq-trans (heq * heq') (heq'' * heq''') = HoriEq-trans heq heq'' * HoriEq-trans heq' heq'''

HoriEq-from-≡ : ∀ {I} (D : RDesc I) → {X : I → Set} {xs : ⟦ D ⟧ X} {xs' : ⟦ D ⟧ X} → xs ≡ xs' → HoriEq D xs D xs'
HoriEq-from-≡ D refl = HoriEq-refl

HoriEq-to-≡ : ∀ {I} (D : RDesc I) → {X : I → Set} (xs : ⟦ D ⟧ X) (xs' : ⟦ D ⟧ X) → HoriEq D xs D xs' → xs ≡ xs'
HoriEq-to-≡ ∎       xs        xs'         heq          = refl
HoriEq-to-≡ (ṿ i)   xs        xs'         (ṿ heq)      = ≅-to-≡ heq
HoriEq-to-≡ (σ S D) (.s , xs) (.s , xs')  (σ s heq)    = cong (_,_ s) (HoriEq-to-≡ (D s) xs xs' heq)
HoriEq-to-≡ (D * E) (xs , ys) (xs' , ys') (heq * heq') = cong₂ _,_ (HoriEq-to-≡ D xs xs' heq) (HoriEq-to-≡ E ys ys' heq')

HoriEq-to-≅ : ∀ {I} (D E : RDesc I) → D ≡ E → {X : I → Set} (xs : ⟦ D ⟧ X) (xs' : ⟦ E ⟧ X) → HoriEq D xs E xs' → xs ≅ xs'
HoriEq-to-≅ D .D refl xs xs' heq = ≡-to-≅ (HoriEq-to-≡ D xs xs' heq)
