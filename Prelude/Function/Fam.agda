-- The category `Fam` of families of sets.
-- An isomorphism between two families of sets in `Fam` can be broken into isomorphisms between corresponding sets in the two families.
-- There is a canonical way of forming pullbacks in `Fam`,
-- namely taking the set-theoretical pullbacks of the index set and corresponding sets in the families.
-- The forgetful functor from `Fam` to `Fun` preserves this pullback, and is hence pullback-preserving.

module Prelude.Function.Fam where

open import Prelude.Equality
open import Prelude.Category
open import Prelude.Category.Isomorphism
open import Prelude.Category.Slice
open import Prelude.Category.Span
open import Prelude.Category.Pullback
open import Prelude.Function
open import Prelude.Product

open import Function using (_∘_; type-signature)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_; <_,_>) renaming (map to _**_)
open import Relation.Binary using (module Setoid)
import Relation.Binary.EqReasoning as EqReasoning
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; subst; cong; cong₂; sym; trans; proof-irrelevance; module ≡-Reasoning) renaming (setoid to ≡-Setoid)
open import Relation.Binary.HeterogeneousEquality
  using (_≅_; ≅-to-≡; ≡-to-≅; ≡-subst-removable; module ≅-Reasoning)
  renaming (refl to hrefl; cong to hcong; cong₂ to hcong₂; sym to hsym; trans to htrans; proof-irrelevance to hproof-irrelevance)

open Functor


FamObject : Set₁
FamObject = Σ[ I ∶ Set ] (I → Set)

infixr 4 _,_

_⇉_ : ∀ {I} → (I → Set) → (I → Set) → Set
X ⇉ Y = ∀ {i} → X i → Y i

infixr 1 _⇉_

record FamMorphism (IX JY : FamObject) : Set₁ where
  constructor _,_
  field
    e : proj₁ IX → proj₁ JY
    u : proj₂ IX ⇉ (proj₂ JY ∘ e)

record FamMorphismEq (IX JY : FamObject) (f g : FamMorphism IX JY) : Set₁ where
  constructor _,_
  field
    e : FamMorphism.e f ≐ FamMorphism.e g
    u : ∀ {i} → FamMorphism.u f {i} ≑ FamMorphism.u g {i}

Fam : Category
Fam = record { Object   = FamObject
             ; Morphism = λ { (I , X) (J , Y) →
                                record { Carrier = FamMorphism (I , X) (J , Y)
                                       ; _≈_ = FamMorphismEq (I , X) (J , Y)
                                       ; isEquivalence =
                                           record { refl  = frefl , ≑-refl
                                                  ; sym   = λ { (eeq , ueq) → fsym eeq , ≑-sym ueq }
                                                  ; trans = λ { (eeq , ueq) (eeq' , ueq') → ftrans eeq eeq' , ≑-trans refl ueq ueq' } } } }
             ; _·_ = λ { (e , u) (f , v) → e ∘ f , u ∘ v }
             ; id     = Function.id , Function.id
             ; id-l   = λ _ → frefl , ≑-refl
             ; id-r   = λ _ → frefl , ≑-refl
             ; assoc  = λ _ _ _ → frefl , ≑-refl
             ; cong-l = λ { {I , X} {J , Y} {K , Z} {e , u} {f , v} (g , w) (eeq , ueq) →
                              fcong-l g eeq ,
                              λ {i} → ≑-cong-l w w (subst (λ j → (x : Y (e i)) (x' : Y j) → x ≅ x' → w x ≅ w x') (eeq i) ≑-refl) ueq }
             ; cong-r = λ { {I , X} {J , Y} {K , Z} {e , u} {f , v} (g , w) (eeq , ueq) →
                              fcong-r g eeq , λ {i} → ≑-cong-r w w ≑-refl ueq } }

FamI : Functor Fam Fun
FamI = record { object   = proj₁
              ; morphism = FamMorphism.e
              ; ≈-respecting    = FamMorphismEq.e
              ; id-preserving   = frefl
              ; comp-preserving = λ _ _ → frefl }

FamF : Functor Fam Fun
FamF = record { object   = λ { (I , X) → Σ I X }
              ; morphism = λ { (e , u) → e ** u }
              ; ≈-respecting    = λ { (eeq , ueq) (i , x) → cong₂-pair (eeq i) (ueq x x hrefl) }
              ; id-preserving   = frefl
              ; comp-preserving = λ { (e , u) (f , v) (i , x) → cong₂-pair refl (≑-refl {f = u ∘ v} x x hrefl) } }

compIso : {I J : Set} {X : I → Set} {Y : J → Set} → (iso : Iso Fam (I , X) (J , Y)) → ∀ i → Iso Fun (X i) (Y (FamMorphism.e (Iso.to Fam iso) i))
compIso {I} {J} {X} {Y} iso i =
  record { to   = FamMorphism.u to
         ; from = λ y → subst X (FamMorphismEq.e from-to-inverse i) (FamMorphism.u from y)
         ; to-from-inverse =
             λ y → ≅-to-≡ (elim-≡ (λ eq → FamMorphism.u to (subst X eq (FamMorphism.u from y)) ≅ y)
                                  (FamMorphismEq.u to-from-inverse y y hrefl) (FamMorphismEq.e from-to-inverse i))
         ; from-to-inverse =
             λ x → ≅-to-≡ (elim-≡ (λ eq → subst X eq (FamMorphism.u from (FamMorphism.u to x)) ≅ x)
                                  (FamMorphismEq.u from-to-inverse x x hrefl) (FamMorphismEq.e from-to-inverse i)) }
  where open Iso Fam iso

compIso-inv : {I J : Set} {X : I → Set} {Y : J → Set} →
              (iso : Iso Fun I J) → (∀ i → Iso Fun (X i) (Y (Iso.to Fun iso i))) → Iso Fam (I , X) (J , Y)
compIso-inv {I} {J} {X} {Y} iso isos =
  record { to   = to iso , λ {i} → to (isos i)
         ; from = from iso , λ {j} y → from (isos (from iso j)) (subst Y (sym (to-from-inverse iso j)) y)
         ; to-from-inverse =
             to-from-inverse iso ,
             λ {i} x x' heq → htrans (≡-to-≅ (to-from-inverse (isos (from iso i)) (subst Y (sym (to-from-inverse iso i)) x)))
                                     (htrans (≡-subst-removable Y (sym (to-from-inverse iso i)) x) heq)
         ; from-to-inverse =
             from-to-inverse iso ,
             λ {i} x x' heq → elim-≡ (λ {i'} eq → (eq' : to iso i ≡ to iso i') → from (isos i') (subst Y eq' (to (isos i) x)) ≅ x')
                                     (λ { refl → htrans (≡-to-≅ (from-to-inverse (isos i) x)) heq })
                                     (sym (from-to-inverse iso i))
                                     (sym (to-from-inverse iso (to iso i))) }
  where open Iso Fun

mkFamIso : {IX JY : FamObject} →
           (idx-iso : Iso Fun (proj₁ IX) (proj₁ JY)) → (∀ i → Iso Fun (proj₂ IX i) (proj₂ JY (Iso.to Fun idx-iso i))) → Iso Fam IX JY
mkFamIso {I , X} {J , Y} idx-iso mem-iso =
  record { to   = Iso.to Fun idx-iso , λ {i} → Iso.to Fun (mem-iso i)
         ; from = Iso.from Fun idx-iso , λ {j} y → Iso.from Fun (mem-iso (Iso.from Fun idx-iso j))
                                                     (subst Y (sym (Iso.to-from-inverse Fun idx-iso j)) y)
         ; to-from-inverse =
             Iso.to-from-inverse Fun idx-iso ,
             λ {j} y y' heq → htrans (≡-to-≅ (Iso.to-from-inverse Fun (mem-iso _)
                                     (subst Y (sym (Iso.to-from-inverse Fun idx-iso j)) y)))
                                     (htrans (≡-subst-removable Y (sym (Iso.to-from-inverse Fun idx-iso j)) y) heq)
         ; from-to-inverse =
             Iso.from-to-inverse Fun idx-iso ,
             λ {i} → pointwise
                       λ x → elim-≡
                               (λ {i'} eq → ∀ eq' → eq' ≡ cong (Iso.to Fun idx-iso) eq →
                                            Iso.from Fun (mem-iso i') (subst Y eq' (Iso.to Fun (mem-iso i) x)) ≅ x)
                               (λ { refl refl → ≡-to-≅ (Iso.from-to-inverse Fun (mem-iso i) x) })
                               (sym (Iso.from-to-inverse Fun idx-iso i))
                               (sym (Iso.to-from-inverse Fun idx-iso (Iso.to Fun idx-iso i)))
                               (proof-irrelevance _ _) }

module CanonicalPullback {B : Category.Object Fam} (f g : Slice Fam B) where

  open Category Fam

  p : Span (SliceCategory Fam B) f g
  p = span (slice (Σ (proj₁ (Slice.T f) × proj₁ (Slice.T g))
                     (λ { (j , k) → FamMorphism.e (Slice.s f) j ≡ FamMorphism.e (Slice.s g) k }) ,
                   λ { ((j , k) , jkeq) →
                       Σ (proj₂ (Slice.T f) j × proj₂ (Slice.T g) k)
                         (λ {(x , y) → FamMorphism.u (Slice.s f) x ≅ FamMorphism.u (Slice.s g) y }) })
                  (FamMorphism.e (Slice.s g) ∘ proj₂ ∘ proj₁ , FamMorphism.u (Slice.s g) ∘ proj₂ ∘ proj₁))
           (sliceMorphism (proj₁ ∘ proj₁ , proj₁ ∘ proj₁) (proj₂ , pointwise proj₂))
           (sliceMorphism (proj₂ ∘ proj₁ , proj₂ ∘ proj₁) (frefl , ≑-refl))

  module Universality (p' : Span (SliceCategory Fam B) f g) where

    assemble : (l : Slice.T (Span.M p') ==> Slice.T f) (r : Slice.T (Span.M p') ==> Slice.T g) →
               Slice.s f · l ≈ Slice.s g · r → Slice.T (Span.M p') ==> Slice.T (Span.M p)
    assemble l r eq = (λ t → (FamMorphism.e l t , FamMorphism.e r t) , FamMorphismEq.e eq t) ,
                      (λ {i} t → (FamMorphism.u l t , FamMorphism.u r t) , FamMorphismEq.u eq t t hrefl)

    p'-to-p : SpanMorphism (SliceCategory Fam B) f g p' p
    p'-to-p =
      spanMorphism
        (let eq = Setoid.trans (Morphism (Slice.T (Span.M p')) B)
                    (SliceMorphism.triangle (Span.l p'))
                    (Setoid.sym (Morphism (Slice.T (Span.M p')) B) (SliceMorphism.triangle (Span.r p')))
             med = assemble (SliceMorphism.m (Span.l p')) (SliceMorphism.m (Span.r p')) eq
         in  sliceMorphism med
               (begin
                  Slice.s (Span.M p) · med
                    ≈⟨ cong-r med (SliceMorphism.triangle (Span.r p)) ⟩
                  (Slice.s g · SliceMorphism.m (Span.r p)) · med
                    ≈⟨ assoc (Slice.s g) (SliceMorphism.m (Span.r p)) med ⟩
                  Slice.s g · (SliceMorphism.m (Span.r p) · med)
                    ≈⟨ Setoid.refl setoid ⟩
                  Slice.s g · SliceMorphism.m (Span.r p')
                    ≈⟨ SliceMorphism.triangle (Span.r p') ⟩
                  Slice.s (Span.M p')
                ∎))
        (Setoid.refl (Morphism (Slice.T (Span.M p')) (Slice.T f)))
        (Setoid.refl (Morphism (Slice.T (Span.M p')) (Slice.T g)))
      where setoid = Morphism (Slice.T (Span.M p')) B
            open EqReasoning setoid

    assemble-inv : (med : Slice.T (Span.M p') ==> Slice.T (Span.M p)) (eq : _) →
                   assemble (SliceMorphism.m (Span.l p) · med) (SliceMorphism.m (Span.r p) · med) eq ≈ med
    assemble-inv med eq = (λ t → cong₂-pair refl (≡-to-≅ (proof-irrelevance _ _))) ,
                          pointwise (λ t → ≡-to-≅ (cong₂-pair refl (≡-to-≅ (hproof-irrelevance _ _))))

    cong-assemble : ∀ {l r l' r' eq eq'} → l ≈ l' → r ≈ r' → assemble l r eq ≈ assemble l' r' eq'
    cong-assemble {l} {r} {l'} {r'} {eq} {eq'} leq req =
      (λ t → aux (FamMorphismEq.e leq t) (FamMorphismEq.e req t)) ,
      λ {i} → pointwise (λ t → aux' (FamMorphismEq.e leq i) (FamMorphismEq.u leq t t hrefl)
                                    (FamMorphismEq.e req i) (FamMorphismEq.u req t t hrefl))
      where aux : ∀ {i i' j j' eq eq'} → i ≡ i' → j ≡ j' →
                  ((i , j) , eq ∶ Σ (proj₁ (Slice.T f) × proj₁ (Slice.T g))
                                  λ { (i , j) → FamMorphism.e (Slice.s f) i ≡ FamMorphism.e (Slice.s g) j })
                    ≡ ((i' , j') ,  eq')
            aux refl refl = cong₂-pair refl (≡-to-≅ (proof-irrelevance _ _))
            aux' : ∀ {i i' j j'}
                   {x : proj₂ (Slice.T f) i} {x' : proj₂ (Slice.T f) i'} {y : proj₂ (Slice.T g) j} {y' : proj₂ (Slice.T g) j'}
                   {eq eq'} → i ≡ i' → x ≅ x' → j ≡ j' → y ≅ y' →
                   ((x , y) , eq ∶ Σ (proj₂ (Slice.T f) i × proj₂ (Slice.T g) j)
                                     λ { (x , y) → FamMorphism.u (Slice.s f) x ≅ FamMorphism.u (Slice.s g) y })
                     ≅ ((x' , y') ,  eq' ∶ Σ (proj₂ (Slice.T f) i' × proj₂ (Slice.T g) j')
                                             λ { (x' , y') → FamMorphism.u (Slice.s f) x' ≅ FamMorphism.u (Slice.s g) y' })
            aux' refl hrefl refl hrefl = ≡-to-≅ (cong₂-pair refl (≡-to-≅ (hproof-irrelevance _ _)))

    uniqueness : Unique (Category.Morphism (SpanCategory (SliceCategory Fam B) f g) p' p) p'-to-p
    uniqueness p'-to'-p =
      let eq  = Setoid.trans (Morphism (Slice.T (Span.M p')) B)
                  (SliceMorphism.triangle (Span.l p'))
                  (Setoid.sym (Morphism (Slice.T (Span.M p')) B) (SliceMorphism.triangle (Span.r p')))
          eq' = cong-r (SliceMorphism.m (SpanMorphism.m p'-to'-p))
                  (Setoid.trans (Morphism (Slice.T (Span.M p)) B)
                                (SliceMorphism.triangle (Span.l p))
                                (Setoid.sym (Morphism (Slice.T (Span.M p)) B) (SliceMorphism.triangle (Span.r p))))
      in begin
           assemble (SliceMorphism.m (Span.l p')) (SliceMorphism.m (Span.r p')) eq
             ≈⟨ Setoid.sym setoid (cong-assemble {eq = eq'} {eq} (SpanMorphism.triangle-l p'-to'-p) (SpanMorphism.triangle-r p'-to'-p)) ⟩
           assemble (SliceMorphism.m (Span.l p) · SliceMorphism.m (SpanMorphism.m p'-to'-p))
                    (SliceMorphism.m (Span.r p) · SliceMorphism.m (SpanMorphism.m p'-to'-p))
                    eq'
             ≈⟨ assemble-inv (SliceMorphism.m (SpanMorphism.m p'-to'-p)) eq' ⟩
           SliceMorphism.m (SpanMorphism.m p'-to'-p)
         ∎
      where setoid = Morphism (Slice.T (Span.M p')) (Slice.T (Span.M p))
            open EqReasoning setoid

module CanonicalPullbackInFun {B' : Category.Object Fam} (f' g' : Slice Fam B') where

  open Category Fun

  B : Set
  B = object FamF B'

  f : Slice Fun B
  f = object (SliceMap FamF) f'

  g : Slice Fun B
  g = object (SliceMap FamF) g'

  p : Span (SliceCategory Fun B) f g
  p = object (SpanMap (SliceMap FamF)) (CanonicalPullback.p f' g')

  module Universality (p' : Span (SliceCategory Fun B) f g) where

    assemble : (l : Slice.T (Span.M p') → Slice.T f) (r : Slice.T (Span.M p') → Slice.T g) →
               Slice.s f ∘ l ≐ Slice.s g ∘ r → Slice.T (Span.M p') → Slice.T (Span.M p)
    assemble l r eq t = ((proj₁ (l t) , proj₁ (r t)) , cong proj₁ (eq t)) , ((proj₂ (l t) , proj₂ (r t)) , hcong proj₂ (≡-to-≅ (eq t)))

    p'-to-p : SpanMorphism (SliceCategory Fun B) f g p' p
    p'-to-p =
      spanMorphism
        (let eq  = ftrans (SliceMorphism.triangle (Span.l p')) (fsym (SliceMorphism.triangle (Span.r p')))
             med = assemble (SliceMorphism.m (Span.l p')) (SliceMorphism.m (Span.r p')) eq
         in  sliceMorphism med
               (begin
                  Slice.s (Span.M p) · med
                    ≈⟨ cong-r med (SliceMorphism.triangle (Span.r p)) ⟩
                  (Slice.s g · SliceMorphism.m (Span.r p)) · med
                    ≈⟨ assoc (Slice.s g) (SliceMorphism.m (Span.r p)) med ⟩
                  Slice.s g · (SliceMorphism.m (Span.r p) · med)
                    ≈⟨ frefl ⟩
                  Slice.s g · SliceMorphism.m (Span.r p')
                    ≈⟨ SliceMorphism.triangle (Span.r p') ⟩
                  Slice.s (Span.M p')
                ∎)) frefl frefl
      where setoid = FunSetoid (Slice.T (Span.M p')) B
            open EqReasoning setoid

    assemble-inv : (med : Slice.T (Span.M p') → Slice.T (Span.M p)) (eq : _) →
                   assemble (SliceMorphism.m (Span.l p) ∘ med) (SliceMorphism.m (Span.r p) ∘ med) eq ≐ med
    assemble-inv med eq t = cong₂-pair (cong₂-pair refl (≡-to-≅ (proof-irrelevance _ _)))
                                       (≡-to-≅ (cong₂-pair refl (≡-to-≅ (hproof-irrelevance _ _))))

    cong-assemble : ∀ {l r l' r' eq eq'} → l ≐ l' → r ≐ r' → assemble l r eq ≐ assemble l' r' eq'
    cong-assemble {l} {r} {l'} {r'} {eq} {eq'} leq req t =
      aux (cong proj₁ (leq t)) (hcong proj₂ (≡-to-≅ (leq t))) (cong proj₁ (req t)) (hcong proj₂ (≡-to-≅ (req t)))
      where aux : ∀ {i i' j j'}
                  {x : proj₂ (Slice.T f') i} {x' : proj₂ (Slice.T f') i'} {y : proj₂ (Slice.T g') j} {y' : proj₂ (Slice.T g') j'} →
                  i ≡ i' → x ≅ x' → j ≡ j' → y ≅ y' → ∀ {ijeq xyeq ijeq' xyeq'} →
                  (((i , j) , ijeq) , ((x , y) , xyeq) ∶ Slice.T (Span.M p)) ≡ (((i' , j') , ijeq') , ((x' , y') , xyeq'))
            aux refl hrefl refl hrefl {ijeq} {xyeq} {ijeq'} {xyeq'} with proof-irrelevance ijeq ijeq' | hproof-irrelevance xyeq xyeq'
            aux refl hrefl refl hrefl {ijeq} {xyeq} {.ijeq} {.xyeq} | refl | refl = refl

    uniqueness : Unique (Category.Morphism (SpanCategory (SliceCategory Fun B) f g) p' p) p'-to-p
    uniqueness p'-to'-p =
      let eq  = ftrans (SliceMorphism.triangle (Span.l p')) (fsym (SliceMorphism.triangle (Span.r p')))
          eq' = fcong-r (SliceMorphism.m (SpanMorphism.m p'-to'-p))
                  (ftrans (SliceMorphism.triangle (Span.l p)) (fsym (SliceMorphism.triangle (Span.r p))))
      in begin
           assemble (SliceMorphism.m (Span.l p')) (SliceMorphism.m (Span.r p')) eq
             ≈⟨ fsym (cong-assemble {eq = eq'} {eq} (SpanMorphism.triangle-l p'-to'-p) (SpanMorphism.triangle-r p'-to'-p)) ⟩
           assemble (SliceMorphism.m (Span.l p) · SliceMorphism.m (SpanMorphism.m p'-to'-p))
                    (SliceMorphism.m (Span.r p) · SliceMorphism.m (SpanMorphism.m p'-to'-p))
                    eq'
             ≈⟨ assemble-inv (SliceMorphism.m (SpanMorphism.m p'-to'-p)) eq' ⟩
           SliceMorphism.m (SpanMorphism.m p'-to'-p)
         ∎
      where setoid = FunSetoid (Slice.T (Span.M p')) (Slice.T (Span.M p))
            open EqReasoning setoid

Mix : {B : Category.Object Fam} (f g : Slice Fam B) → FamObject
Mix f g = Slice.T (Span.M (CanonicalPullback.p f g))

canonPullback : {B : Category.Object Fam} (f g : Slice Fam B) → Pullback Fam f g (Mix f g)
canonPullback f g = (CanonicalPullback.p f g , refl) ,
                    λ p' → CanonicalPullback.Universality.p'-to-p f g p' , CanonicalPullback.Universality.uniqueness f g p'

module PullbackPreserving
  {B : Category.Object Fam} (f g : Slice Fam B)
  (p : Span (SliceCategory Fam B) f g) (term-p : Terminal (SpanCategory (SliceCategory Fam B) f g) p) where

  B' : Set
  B' = object FamF B

  f' : Slice Fun B'
  f' = object (SliceMap FamF) f

  g' : Slice Fun B'
  g' = object (SliceMap FamF) g

  p' : Span (SliceCategory Fun B') f' g'
  p' = object (SpanMap (SliceMap FamF)) p

  c : Span (SliceCategory Fam B) f g
  c = CanonicalPullback.p f g

  c' : Span (SliceCategory Fun B') f' g'
  c' = CanonicalPullbackInFun.p f g

  p-to-c : SpanMorphism (SliceCategory Fam B) f g p c
  p-to-c = CanonicalPullback.Universality.p'-to-p f g p

  p'-to-c' : SpanMorphism (SliceCategory Fun B') f' g' p' c'
  p'-to-c' = morphism (SpanMap (SliceMap FamF)) p-to-c

  module Universality (q' : Span (SliceCategory Fun B') f' g') where

    open Category (SpanCategory (SliceCategory Fun B') f' g')

    q'-to-c' : SpanMorphism (SliceCategory Fun B') f' g' q' c'
    q'-to-c' = CanonicalPullbackInFun.Universality.p'-to-p f g q'

    c-to-p : SpanMorphism (SliceCategory Fam B) f g c p
    c-to-p = proj₁ (term-p c)

    c'-to-p' : SpanMorphism (SliceCategory Fun B') f' g' c' p'
    c'-to-p' = morphism (SpanMap (SliceMap FamF)) c-to-p

    q'-to-p' : SpanMorphism (SliceCategory Fun B') f' g' q' p'
    q'-to-p' = c'-to-p' · q'-to-c'

    module Uniqueness (q'-to'-p' : SpanMorphism (SliceCategory Fun B') f' g' q' p') where

      q'-to'-c' : SpanMorphism (SliceCategory Fun B') f' g' q' c'
      q'-to'-c' = p'-to-c' · q'-to'-p'

      inverse : c'-to-p' · p'-to-c' ≈ id
      inverse =
        begin
          c'-to-p' · p'-to-c'
            ≈⟨ Setoid.refl (Morphism p' p') {c'-to-p' · p'-to-c'} ⟩
          morphism (SpanMap (SliceMap FamF)) c-to-p · morphism (SpanMap (SliceMap FamF)) p-to-c
            ≈⟨ Setoid.sym setoid
                 {morphism (SpanMap (SliceMap FamF)) (c-to-p ·′ p-to-c)}
                 {morphism (SpanMap (SliceMap FamF)) c-to-p · morphism (SpanMap (SliceMap FamF)) p-to-c}
                 (comp-preserving (SpanMap (SliceMap FamF)) c-to-p p-to-c) ⟩
          morphism (SpanMap (SliceMap FamF)) (c-to-p ·′ p-to-c)
            ≈⟨ ≈-respecting (SpanMap (SliceMap FamF)) {_} {_} {c-to-p ·′ p-to-c} {id′}
                 (equal (Category.Morphism (SpanCategory (SliceCategory Fam B) f g) p p) (term-p p) (c-to-p ·′ p-to-c) id′) ⟩
          morphism (SpanMap (SliceMap FamF)) {p} id′
            ≈⟨ id-preserving (SpanMap (SliceMap FamF)) {p} ⟩
          id
        ∎
        where open Category (SpanCategory (SliceCategory Fam B) f g) using () renaming (_·_ to _·′_; id to id′)
              setoid = Morphism p' p'
              open EqReasoning setoid

      uniqueness : q'-to-p' ≈ q'-to'-p'
      uniqueness =
        begin
          q'-to-p'
            ≈⟨ Setoid.refl (Morphism q' p') {q'-to-p'} ⟩
          c'-to-p' · q'-to-c'
            ≈⟨ cong-l {_} {_} {_} {q'-to-c'} {p'-to-c' · q'-to'-p'} c'-to-p'
                 (CanonicalPullbackInFun.Universality.uniqueness f g q' q'-to'-c') ⟩
          c'-to-p' · (p'-to-c' · q'-to'-p')
            ≈⟨ Setoid.sym setoid
                 {(c'-to-p' · p'-to-c') · q'-to'-p'} {c'-to-p' · (p'-to-c' · q'-to'-p')}
                 (assoc c'-to-p' p'-to-c' q'-to'-p') ⟩
          (c'-to-p' · p'-to-c') · q'-to'-p'
            ≈⟨ cong-r {_} {_} {_} {c'-to-p' · p'-to-c'} {id} q'-to'-p' inverse ⟩
          id · q'-to'-p'
            ≈⟨ id-l q'-to'-p' ⟩
          q'-to'-p'
        ∎
        where setoid = Morphism q' p'
              open EqReasoning setoid

FamF-preserves-pullback : Pullback-preserving FamF
FamF-preserves-pullback f g ._ ((p , refl) , term-p) =
  λ q' → PullbackPreserving.Universality.q'-to-p' f g p term-p q' ,
         PullbackPreserving.Universality.Uniqueness.uniqueness f g p term-p q'
