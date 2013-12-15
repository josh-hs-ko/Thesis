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

open import Function using (id; const)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; inspect; [_])


ListRAlg : Set → Set → Set₁
ListRAlg A X = Ḟ ⌊ ListOD A ⌋ (const X) ↝ const X

AlgList : (A : Set) {X : Set} → ListRAlg A X → X → Set
AlgList A R x = μ ⌊ algOrn ⌊ ListOD A ⌋ R ⌋ (tt , x)

ListAlg : Set → Set → Set
ListAlg A X = Ḟ ⌊ ListOD A ⌋ (const X) ⇉ const X

ListCoAlg : Set → Set → Set
ListCoAlg A X = const X ⇉ Ḟ ⌊ ListOD A ⌋ (const X)

nothing : {A X : Set} → Ḟ ⌊ ListOD A ⌋ (const X) tt
nothing = `nil , tt

next : {A X : Set} → A → X → Ḟ ⌊ ListOD A ⌋ (const X) tt
next a x = `cons , a , x , tt

foldl-alg : {B X : Set} → (X → B → X) → ListAlg B (X → X)
foldl-alg g (`nil  ,          tt) = id
foldl-alg g (`cons , a , g' , tt) = λ x → g' (g x a)

foldl : {B X : Set} → (X → B → X) → X → List B → X
foldl g x bs = fold (foldl-alg g) bs x

StreamingCondition : {A B X : Set} (f : ListCoAlg A X) (g : X → B → X) → Set
StreamingCondition {A} {B} {X} f g = (a : A) (b : B) (x x' : X) → f x ≡ next a x' → f (g x b) ≡ next a (g x' b)

data Accessible {A X : Set} (f : ListCoAlg A X) : X → Set where
  rec : {x : X} → ((a : A) (x' : X) → f x ≡ next a x' → Accessible f x') → Accessible f x

WellFounded : {A X : Set} (f : ListCoAlg A X) → Set
WellFounded {A} {X} f = (x : X) → Accessible f x

module StreamingTheorem {A B X : Set} (f : ListCoAlg A X) (wf : WellFounded f) (g : X → B → X) (cond : StreamingCondition f g) where

  streaming-lemma : (a : A) (x x' : X) → f x ≡ next a x' → {h : X → X} (bs : AlgList B (fun (foldl-alg g)) h) → f (h x) ≡ next a (h x')
  streaming-lemma a x x' eq (con (`nil  ,     tt       , refl ,      tt)) = eq
  streaming-lemma a x x' eq (con (`cons , b , (h , tt) , refl , bs , tt)) = streaming-lemma a (g x b) (g x' b) (cond a b x x' eq) bs

  stream-aux : (x : X) → Accessible f x → {h : X → X} → AlgList B (fun (foldl-alg g)) h → AlgList A (fun f º) (h x)
  stream-aux x acc            bs                                            with f x                | inspect f x
  stream-aux x acc            (con (`nil  ,     tt       , refl ,      tt)) | (`nil  ,          tt) | [ fxeq ] = con (`nil , tt , fxeq , tt)
  stream-aux x acc            (con (`cons , b , (h , tt) , refl , bs , tt)) | (`nil  ,          tt) | [ fxeq ] = stream-aux (g x b) (wf (g x b)) bs
  stream-aux x (rec accs) {h} bs                                            | (`cons , a , x' , tt) | [ fxeq ] = con (`cons , a , (h x' , tt) ,
                                                                                                                      streaming-lemma a x x' fxeq bs ,
                                                                                                                      stream-aux x' (accs a x' fxeq) bs , tt)

  stream : (x : X) → {h : X → X} → AlgList B (fun (foldl-alg g)) h → AlgList A (fun f º) (h x)
  stream x bs = stream-aux x (wf x) bs

  {- not considering termination:

  stream : (x : X) {h : X → X} → AlgList B (fun (foldl-alg g)) h → AlgList A (fun f º) (h x)
  stream f g cond x     bs                                            with f x                | inspect f x
  stream f g cond x     (con (`nil  ,     tt       , refl ,      tt)) | (`nil  ,          tt) | [ fxeq ] = con (`nil , tt , fxeq , tt)
  stream f g cond x     (con (`cons , b , (h , tt) , refl , bs , tt)) | (`nil  ,          tt) | [ fxeq ] = stream (g x b) bs
  stream f g cond x {h} bs                                            | (`cons , a , x' , tt) | [ fxeq ] = con (`cons , a , (h x' , tt) ,
                                                                                                                streaming-lemma a x x' fxeq bs ,
                                                                                                                stream f g cond x' bs , tt)

  -}

  producer-ref : (x : X) (bs : List B) → Refinement (List A) (AlgList A (fun f º) (foldl g x bs))
  producer-ref x bs = FRefinement.comp (toFRefinement (algOrn-FSwap ⌊ ListOD A ⌋ (fun f º))) (ok (tt , foldl g x bs))

  consumer-ref : (bs : List B) → Refinement (List B) (AlgList B (fun (foldl-alg g)) (fold (foldl-alg g) bs))
  consumer-ref bs = FRefinement.comp (toFRefinement (algOrn-FSwap ⌊ ListOD B ⌋ (fun (foldl-alg g)))) (ok (tt , fold (foldl-alg g) bs))

  stream'-aux : (x : X) (bs : List B) → AlgList A (fun f º) (foldl g x bs)
  stream'-aux x bs = stream x (Iso.from (Refinement.i (consumer-ref bs)) (bs , foldR'-fun-computation (foldl-alg g) bs))

  stream' : X → List B → List A
  stream' x bs = Refinement.forget (producer-ref x bs) (stream'-aux x bs)

  streaming-theorem : (x : X) → foldR (fun f º) º • fun (foldl g x) ⊇ fun (stream' x)
  streaming-theorem x = wrap λ _ → wrap λ { bs ._ refl → foldl g x bs , refl , proj₂ (Iso.to (Refinement.i (producer-ref x bs)) (stream'-aux x bs)) }
