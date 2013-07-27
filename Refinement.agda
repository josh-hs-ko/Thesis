-- Definition of refinements, swaps, and upgrades.

module Refinement where

open import Prelude.Function
open import Prelude.Function.Fam
import Prelude.Category.Isomorphism as Isomorphism; open Isomorphism Fun
open import Prelude.Product
open import Prelude.InverseImage
open import Prelude.Equality

open import Function using (id; _∘_; const)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; <_,_>; uncurry) renaming (map to _**_)
open import Relation.Binary using (module Setoid)
import Relation.Binary.EqReasoning as EqReasoning
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; cong; sym; trans)
open import Relation.Binary.HeterogeneousEquality using (_≅_; ≅-to-≡; ≡-to-≅; ≡-subst-removable) renaming (cong to hcong; trans to htrans)


--------
-- refinements

record Refinement (X Y : Set) : Set₁ where
  field
    P : X → Set
    i : Iso Y (Σ X P)
  forget : Y → X
  forget = proj₁ ∘ Iso.to i

Ref-refl : {X : Set} → Refinement X X
Ref-refl = record { P = const ⊤
                  ; i = record { to   = < id , const tt >
                               ; from = proj₁
                               ; to-from-inverse = frefl
                               ; from-to-inverse = frefl } }

Ref-trans : {X Y Z : Set} → Refinement X Y → Refinement Y Z → Refinement X Z
Ref-trans {X} {Y} {Z} r s =
  record { P = λ x → Σ[ p ∶ Refinement.P r x ] Refinement.P s (Iso.from (Refinement.i r) (x , p))
         ; i = begin
                 Z
                   ≅⟨ Refinement.i s ⟩
                 Σ Y (Refinement.P s)
                   ≅⟨ fstIso (Refinement.i r) ⟩
                 Σ (Σ X (Refinement.P r)) (Refinement.P s ∘ Iso.from (Refinement.i r))
                   ≅⟨ Σ-assoc (Refinement.P r) (Refinement.P s ∘ Iso.from (Refinement.i r)) ⟩
                 Σ X (Σ' (Refinement.P r) (Refinement.P s ∘ Iso.from (Refinement.i r)))
               □ }
  where open EqReasoning IsoSetoid renaming (_≈⟨_⟩_ to _≅⟨_⟩_; _∎ to _□)

canonRef : {X Y : Set} → (Y → X) → Refinement X Y
canonRef {X} {Y} f =
  record { P = λ x → Σ[ y ∶ Y ] f y ≡ x
         ; i = record { to   = < f , < id , frefl > >
                      ; from = proj₁ ∘ proj₂
                      ; to-from-inverse = λ { (._ , y , refl) → refl }
                      ; from-to-inverse = frefl } }

prom-change : {X Y : Set} (r s : Refinement X Y) → Refinement.forget r ≐ Refinement.forget s →
              ∀ x → Refinement.P r x → Refinement.P s x
prom-change r s eq x p =
  subst (Refinement.P s)
        (trans (sym (eq (Iso.from (Refinement.i r) (x , p)))) (cong proj₁ (Iso.to-from-inverse (Refinement.i r) (x , p))))
        (proj₂ (Iso.to (Refinement.i s) (Iso.from (Refinement.i r) (x , p))))

prom-inverse : {X Y : Set} (r s : Refinement X Y)
               (rseq : Refinement.forget r ≐ Refinement.forget s) (sreq : Refinement.forget s ≐ Refinement.forget r) →
               ∀ x (p : Refinement.P r x) → prom-change s r sreq x (prom-change r s rseq x p) ≡ p
prom-inverse r s rseq sreq x p =
  let xp = (x , subst (Refinement.P s)
                      (trans (sym (rseq (Iso.from (Refinement.i r) (x , p))))
                             (cong proj₁ (Iso.to-from-inverse (Refinement.i r) (x , p))))
                      (proj₂ (Iso.to (Refinement.i s) (Iso.from (Refinement.i r) (x , p)))))
  in  ≅-to-≡ (htrans (≡-subst-removable (Refinement.P r)
                                        (trans (sym (sreq (Iso.from (Refinement.i s) xp)))
                                               (cong proj₁ (Iso.to-from-inverse (Refinement.i s) xp)))
                                        (proj₂ (Iso.to (Refinement.i r) (Iso.from (Refinement.i s) xp))))
                     (elim-≡ (λ {x'} eq' →
                                proj₂ (Iso.to (Refinement.i r) (Iso.from (Refinement.i s)
                                  (x' , subst (Refinement.P s) eq'
                                              (proj₂ (Iso.to (Refinement.i s) (Iso.from (Refinement.i r) (x , p)))))))
                                ≅ p)
                             (htrans (hcong (proj₂ ∘ Iso.to (Refinement.i r))
                                       (≡-to-≅ (Iso.from-to-inverse (Refinement.i s) (Iso.from (Refinement.i r) (x , p)))))
                                     (hcong proj₂ (≡-to-≅ (Iso.to-from-inverse (Refinement.i r) (x , p)))))
                             (trans (sym (rseq (Iso.from (Refinement.i r) (x , p))))
                                    (cong proj₁ (Iso.to-from-inverse (Refinement.i r) (x , p))))))

promIso : {X Y : Set} (r s : Refinement X Y) → Refinement.forget r ≐ Refinement.forget s →
          ∀ x → Iso (Refinement.P r x) (Refinement.P s x)
promIso r s eq x =
  record { to   = prom-change r s eq x
         ; from = prom-change s r (fsym eq) x
         ; to-from-inverse = prom-inverse s r (fsym eq) eq x
         ; from-to-inverse = prom-inverse r s eq (fsym eq) x }

coherence : {X Y : Set} (r : Refinement X Y) → ∀ x → Iso (Refinement.P r x) (Σ[ y ∶ Y ] Refinement.forget r y ≡ x)
coherence {X} {Y} r = promIso r (canonRef (Refinement.forget r)) frefl

record FRefinement {I J : Set} (e : J → I) (X : I → Set) (Y : J → Set) : Set₁ where
  constructor wrap
  field
    comp : ∀ {i} (j : e ⁻¹ i) → Refinement (X i) (Y (und j))
  forget : Y ⇉ (X ∘ e)
  forget {j} = Refinement.forget (comp (ok j))

FRef-refl : ∀ {I} {X : I → Set} → FRefinement id X X
FRef-refl = wrap λ { {._} (ok i) → Ref-refl }

FRef-trans : ∀ {I J K} {e : J → I} {f : K → J} {X Y Z} → FRefinement e X Y → FRefinement f Y Z → FRefinement (e ∘ f) X Z
FRef-trans {f = f} r s = wrap λ { {._} (ok k) → Ref-trans (FRefinement.comp r (ok (f k))) (FRefinement.comp s (ok k)) }

canonFRef : ∀ {I J} {e : J → I} {X Y} → Y ⇉ (X ∘ e) → FRefinement e X Y
canonFRef f = wrap λ { {._} (ok j) → canonRef f }


--------
-- predicate swaps

record Swap {X Y : Set} (r : Refinement X Y) : Set₁ where
  field
    Q : X → Set
    s : ∀ x → Iso (Refinement.P r x) (Q x)

toRefinement : {X Y : Set} {r : Refinement X Y} → Swap r → Refinement X Y
toRefinement {r = r} s =
  record { P = Swap.Q s
         ; i = Setoid.trans IsoSetoid
                 (Refinement.i r)
                 (record { to   = id ** (λ {x} → Iso.to (Swap.s s x))
                         ; from = id ** (λ {x} → Iso.from (Swap.s s x))
                         ; to-from-inverse = λ { (x , q) → cong (_,_ x) (Iso.to-from-inverse (Swap.s s x) _) }
                         ; from-to-inverse = λ { (x , p) → cong (_,_ x) (Iso.from-to-inverse (Swap.s s x) _) } }) }

idSwap : {X Y : Set} {r : Refinement X Y} → Swap r
idSwap {r = r} = record { Q = Refinement.P r
                        ; s = λ _ → Setoid.refl IsoSetoid }

record FSwap {I J : Set} {e : J → I} {X : I → Set} {Y : J → Set} (r : FRefinement e X Y) : Set₁ where
  constructor wrap
  field
    comp : ∀ {i} (j : e ⁻¹ i) → Swap (FRefinement.comp r j)

toFRefinement : {I J : Set} {e : J → I} {X : I → Set} {Y : J → Set} {r : FRefinement e X Y} → FSwap r → FRefinement e X Y
toFRefinement (wrap s) = wrap (toRefinement ∘ s)

idFSwap : {I J : Set} {e : J → I} {X : I → Set} {Y : J → Set} {r : FRefinement e X Y} → FSwap r
idFSwap {r = r} = wrap λ _ → idSwap


--------
-- upgrades

record Upgrade (X Y : Set) : Set₁ where
  field
    P : X → Set
    C : X → Y → Set
    u : ∀ x → P x → Y
    c : ∀ x → (p : P x) → C x (u x p)

toUpgrade : ∀ {X Y} → Refinement X Y → Upgrade X Y
toUpgrade r = record { P = Refinement.P r
                     ; C = λ x y → Refinement.forget r y ≡ x
                     ; u = λ x → proj₁ ∘ Iso.to (coherence r x)
                     ; c = λ x → proj₂ ∘ Iso.to (coherence r x) }

_⇀_ : {X Y Z W : Set} → Refinement X Y → Upgrade Z W → Upgrade (X → Z) (Y → W)
r ⇀ s = record { P = λ f → ∀ x → (p : Refinement.P r x) → Upgrade.P s (f x)
               ; C = λ f g → ∀ x y → Upgrade.C (toUpgrade r) x y → Upgrade.C s (f x) (g y)
               ; u = λ f h → Upgrade.u s _ ∘ uncurry h ∘ Iso.to (Refinement.i r)
               ; c = λ { f h ._ y refl → let xp = (Iso.to (Refinement.i r) y)
                                         in  Upgrade.c s (f (proj₁ xp)) (uncurry h xp) } }

infixr 2 _⇀_

new : {X : Set} (I : Set) {Y : I → Set} → (∀ i → Upgrade X (Y i)) → Upgrade X ((i : I) → Y i)
new I r = record { P = λ x → ∀ i → Upgrade.P (r i) x
                 ; C = λ x y → ∀ i → Upgrade.C (r i) x (y i)
                 ; u = λ x p i → Upgrade.u (r i) x (p i)
                 ; c = λ x p i → Upgrade.c (r i) x (p i) }

syntax new I (λ i → r) = ∀⁺[ i ∶ I ] r

new' : {X : Set} (I : Set) {Y : I → Set} → (∀ i → Upgrade X (Y i)) → Upgrade X ({i : I} → Y i)
new' I r = record { P = λ x → ∀ {i} → Upgrade.P (r i) x
                  ; C = λ x y → ∀ {i} → Upgrade.C (r i) x (y {i})
                  ; u = λ x p {i} → Upgrade.u (r i) x (p {i})
                  ; c = λ x p {i} → Upgrade.c (r i) x (p {i}) }

syntax new' I (λ i → r) = ∀⁺[[ i ∶ I ]] r

fixed : (I : Set) {X : I → Set} {Y : I → Set} → (∀ i → Upgrade (X i) (Y i)) → Upgrade ((i : I) → X i) ((i : I) → Y i)
fixed I u = record { P = λ f → ∀ i → Upgrade.P (u i) (f i)
                   ; C = λ f g → ∀ i → Upgrade.C (u i) (f i) (g i)
                   ; u = λ f h i → Upgrade.u (u i) (f i) (h i)
                   ; c = λ f h i → Upgrade.c (u i) (f i) (h i) }

syntax fixed I (λ i → u) = ∀[ i ∶ I ] u

fixed' : (I : Set) {X : I → Set} {Y : I → Set} → (∀ i → Upgrade (X i) (Y i)) → Upgrade ({i : I} → X i) ({i : I} → Y i)
fixed' I u = record { P = λ f → ∀ {i} → Upgrade.P (u i) (f {i})
                    ; C = λ f g → ∀ {i} → Upgrade.C (u i) (f {i}) (g {i})
                    ; u = λ f h {i} → Upgrade.u (u i) (f {i}) (h {i}) 
                    ; c = λ f h {i} → Upgrade.c (u i) (f {i}) (h {i}) }

syntax fixed' I (λ i → u) = ∀[[ i ∶ I ]] u

_′⇀_ : {I J : Set} {X : I → Set} {Y : J → Set} →
     (r : Refinement I J) → (∀ i j → Upgrade.C (toUpgrade r) i j → Upgrade (X i) (Y j)) → Upgrade ((i : I) → X i) ((j : J) → Y j)
r ′⇀ s = record { P = λ f → ∀ i j → (c : Upgrade.C (toUpgrade r) i j) → Upgrade.P (s i j c) (f i)
                ; C = λ f g → ∀ i j → (c : Upgrade.C (toUpgrade r) i j) → Upgrade.C (s i j c) (f i) (g j)
                ; u = λ f h j → let i = proj₁ (Iso.to (Refinement.i r) j)
                                in  Upgrade.u (s i j refl) (f i) (h i j refl)
                ; c = λ { f h ._ j refl → let i = proj₁ (Iso.to (Refinement.i r) j)
                                          in  Upgrade.c (s i j refl) (f i) (h i j refl) } }
