-- Implementing the streaming theorem for list metamorphisms by algebraic ornamentation.

module Examples.Metamorphism where

open import Prelude.Function
import Prelude.Category.Isomorphism as Isomorphism; open Isomorphism Fun
open import Prelude.Function.Fam
open import Prelude.InverseImage
open import Refinement
open import Description
open import Ornament
open import Ornament.Algebraic
open import Relation
open import Relation.Fold
open import Examples.Nat
open import Examples.List

open import Function using (id; _∘_; const; flip)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; Σ-syntax; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; inspect; [_])


ListRAlg : Set → Set → Set₁
ListRAlg A X = Ḟ ⌊ ListOD A ⌋ (const X) ↝ const X

AlgList : (A : Set) {X : Set} → ListRAlg A X → X → Set
AlgList A R x = μ ⌊ algOrn ⌊ ListOD A ⌋ R ⌋ (tt , x)

ListAlg : Set → Set → Set
ListAlg A X = Ḟ ⌊ ListOD A ⌋ (const X) ⇉ const X

ListCoAlg : Set → Set → Set
ListCoAlg A X = const X ⇉ Ḟ ⌊ ListOD A ⌋ (const X)

next : {A X : Set} → A → X → Ḟ ⌊ ListOD A ⌋ (const X) tt
next a x = `cons , a , x , tt

foldl-alg : {A X : Set} → (X → A → X) → ListAlg A (X → X)
foldl-alg f (`nil  ,          tt) = id
foldl-alg f (`cons , a , f' , tt) = f' ∘ flip f a

foldl : {A X : Set} → (X → A → X) → X → List A → X
foldl f x as = fold (foldl-alg f) as x

StreamingCondition : {A B X : Set} (f : X → A → X) (g : ListCoAlg B X) → Set
StreamingCondition {A} {B} {X} f g = (a : A) (b : B) (x x' : X) → g x ≡ next b x' → g (f x a) ≡ next b (f x' a)

data Accessible {B X : Set} (g : ListCoAlg B X) : X → Set where
  rec : {x : X} → ((b : B) (x' : X) → g x ≡ next b x' → Accessible g x') → Accessible g x

WellFounded : {B X : Set} (g : ListCoAlg B X) → Set
WellFounded {B} {X} g = (x : X) → Accessible g x

module StreamingTheorem {A B X : Set} (f : X → A → X) (g : ListCoAlg B X) (wf : WellFounded g) (cond : StreamingCondition f g) where

  streaming-lemma : (b : B) (x x' : X) → g x ≡ next b x' → {h : X → X} (as : AlgList A (fun (foldl-alg f)) h) → g (h x) ≡ next b (h x')
  streaming-lemma b x x' eq (con (`nil  ,     tt       , refl ,      tt)) = eq
  streaming-lemma b x x' eq (con (`cons , a , (h , tt) , refl , as , tt)) = streaming-lemma b (f x a) (f x' a) (cond a b x x' eq) as

  stream-aux : (x : X) → Accessible g x → {h : X → X} → AlgList A (fun (foldl-alg f)) h → AlgList B (fun g º) (h x)
  stream-aux x acc            as                                            with g x                | inspect g x
  stream-aux x acc            (con (`nil  ,     tt       , refl ,      tt)) | (`nil  ,          tt) | [ gxeq ] = con (`nil , tt , gxeq , tt)
  stream-aux x acc            (con (`cons , a , (h , tt) , refl , as , tt)) | (`nil  ,          tt) | [ gxeq ] = stream-aux (f x a) (wf (f x a)) as
  stream-aux x (rec accs) {h} as                                            | (`cons , b , x' , tt) | [ gxeq ] = con (`cons , b , (h x' , tt) ,
                                                                                                                      streaming-lemma b x x' gxeq as ,
                                                                                                                      stream-aux x' (accs b x' gxeq) as , tt)

  stream : (x : X) → {h : X → X} → AlgList A (fun (foldl-alg f)) h → AlgList B (fun g º) (h x)
  stream x as = stream-aux x (wf x) as

  {- not considering termination:

  stream : (x : X) {h : X → X} → AlgList A (fun (foldl-alg f)) h → AlgList B (fun g º) (h x)
  stream x     as                                            with g x                | inspect g x
  stream x     (con (`nil  ,     tt       , refl ,      tt)) | (`nil  ,          tt) | [ gxeq ] = con (`nil , tt , gxeq , tt)
  stream x     (con (`cons , a , (h , tt) , refl , as , tt)) | (`nil  ,          tt) | [ gxeq ] = stream (f x a) as
  stream x {h} as                                            | (`cons , b , x' , tt) | [ gxeq ] = con (`cons , b , (h x' , tt) ,
                                                                                                       streaming-lemma b x x' gxeq as ,
                                                                                                       stream x' as , tt)

  -}

  producer-ref : (x : X) (as : List A) → Refinement (List B) (AlgList B (fun g º) (foldl f x as))
  producer-ref x as = FRefinement.comp (toFRefinement (algOrn-FSwap ⌊ ListOD B ⌋ (fun g º))) (ok (tt , foldl f x as))

  consumer-ref : (as : List A) → Refinement (List A) (AlgList A (fun (foldl-alg f)) (fold (foldl-alg f) as))
  consumer-ref as = FRefinement.comp (toFRefinement (algOrn-FSwap ⌊ ListOD A ⌋ (fun (foldl-alg f)))) (ok (tt , fold (foldl-alg f) as))

  stream'-aux : (x : X) (as : List A) → AlgList B (fun g º) (foldl f x as)
  stream'-aux x as = stream x (Iso.from (Refinement.i (consumer-ref as)) (as , foldR'-fun-computation (foldl-alg f) as))

  stream' : X → List A → List B
  stream' x as = Refinement.forget (producer-ref x as) (stream'-aux x as)

  streaming-theorem : (x : X) → foldR (fun g º) º • fun (foldl f x) ⊇ fun (stream' x)
  streaming-theorem x = wrap λ _ → wrap λ { as ._ refl → foldl f x as , refl , proj₂ (Iso.to (Refinement.i (producer-ref x as)) (stream'-aux x as)) }
