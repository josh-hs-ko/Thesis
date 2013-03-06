-- An inductively defined equivalence between description-based data that poses little restriction on their actual types.

module Thesis.Description.HorizontalEquivalence where

open import Thesis.Description

open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; _×_)
open import Data.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)
open import Relation.Binary.HeterogeneousEquality using (_≅_; ≅-to-≡; ≡-to-≅) renaming (refl to hrefl; sym to hsym; trans to htrans)


ṀEq : {I : Set} {X Y : I → Set} (is : List I) → Ṁ X is → Ṁ Y is → Set
ṀEq []       _        _        = ⊤
ṀEq (i ∷ is) (x , xs) (y , ys) = x ≅ y × ṀEq is xs ys

data HoriEq {I : Set} {X Y : I → Set} : (D : RDesc I) → ⟦ D ⟧ X → (E : RDesc I) → ⟦ E ⟧ Y → Set₁ where
  ṿ   : {is : List I} {xs : Ṁ X is} {ys : Ṁ Y is} → ṀEq is xs ys → HoriEq (ṿ is) xs (ṿ is) ys
  σ   : {S : Set} (s : S) → ∀ {D E xs ys} → HoriEq (D s) xs (E s) ys → HoriEq (σ S D) (s , xs) (σ S E) (s , ys)

HoriEq-refl : {I : Set} {D : RDesc I} {X : I → Set} {xs : ⟦ D ⟧ X} → HoriEq D xs D xs
HoriEq-refl {I} {ṿ is } {X} {xs    } = ṿ (aux is xs)
 where
   aux : (is : List I) (xs : Ṁ X is) → ṀEq is xs xs
   aux []       _        = tt
   aux (i ∷ is) (x , xs) = hrefl , aux is xs
HoriEq-refl {I} {σ S D} {X} {s , xs} = σ s HoriEq-refl

HoriEq-sym : {I : Set} {D E : RDesc I} {X Y : I → Set} {xs : ⟦ D ⟧ X} {ys : ⟦ E ⟧ Y} → HoriEq D xs E ys → HoriEq E ys D xs
HoriEq-sym {I} {X = X} {Y} (ṿ heqs)  = ṿ (aux _ _ _ heqs)
  where
    aux : (is : List I) (xs : Ṁ X is) (ys : Ṁ Y is) → ṀEq is xs ys → ṀEq is ys xs
    aux []       _        _        _            = tt
    aux (i ∷ is) (x , xs) (y , ys) (heq , heqs) = hsym heq , aux is xs ys heqs
HoriEq-sym                 (σ s heq) = σ s (HoriEq-sym heq)

HoriEq-trans : {I : Set} {D E F : RDesc I} {X Y Z : I → Set} {xs : ⟦ D ⟧ X} {ys : ⟦ E ⟧ Y} {zs : ⟦ F ⟧ Z} →
               HoriEq D xs E ys → HoriEq E ys F zs → HoriEq D xs F zs
HoriEq-trans {I} {X = X} {Y} {Z} (ṿ heqs)     (ṿ heqs')   = ṿ (aux _ _ _ _ heqs heqs')
  where
    aux : (is : List I) (xs : Ṁ X is) (ys : Ṁ Y is) (zs : Ṁ Z is) → ṀEq is xs ys → ṀEq is ys zs → ṀEq is xs zs
    aux []       _        _        _        _            _              = tt
    aux (i ∷ is) (x , xs) (y , ys) (z , zs) (heq , heqs) (heq' , heqs') = htrans heq heq' , aux is xs ys zs heqs heqs'
HoriEq-trans                     (σ s heq)    (σ .s heq') = σ s (HoriEq-trans heq heq')

HoriEq-from-≡ : ∀ {I} (D : RDesc I) → {X : I → Set} {xs : ⟦ D ⟧ X} {xs' : ⟦ D ⟧ X} → xs ≡ xs' → HoriEq D xs D xs'
HoriEq-from-≡ D refl = HoriEq-refl

HoriEq-to-≡ : ∀ {I} (D : RDesc I) → {X : I → Set} (xs : ⟦ D ⟧ X) (xs' : ⟦ D ⟧ X) → HoriEq D xs D xs' → xs ≡ xs'
HoriEq-to-≡ (ṿ [])       _         _          _                = refl
HoriEq-to-≡ (ṿ (i ∷ is)) (x , xs)  (x' , xs') (ṿ (heq , heqs)) = cong₂ _,_ (≅-to-≡ heq) (HoriEq-to-≡ (ṿ is) xs xs' (ṿ heqs))
HoriEq-to-≡ (σ S D)      (.s , xs) (.s , xs') (σ s heq)        = cong (_,_ s) (HoriEq-to-≡ (D s) xs xs' heq)

HoriEq-to-≅ : ∀ {I} (D E : RDesc I) → D ≡ E → {X : I → Set} (xs : ⟦ D ⟧ X) (xs' : ⟦ E ⟧ X) → HoriEq D xs E xs' → xs ≅ xs'
HoriEq-to-≅ D .D refl xs xs' heq = ≡-to-≅ (HoriEq-to-≡ D xs xs' heq)
