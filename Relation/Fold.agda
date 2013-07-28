-- Definition and properties of relational fold.

module Relation.Fold where

open import Prelude.Category.Isomorphism
open import Prelude.Function
open import Prelude.Function.Fam
open import Description
open import Relation
open import Relation.CompChain

open import Function using (id; _∘_)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary using (module Setoid)
import Relation.Binary.EqReasoning as EqReasoning
import Relation.Binary.PreorderReasoning as PreorderReasoning
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; subst)


mutual

  foldR' : {I : Set} {D : Desc I} {X : I → Set} → (Ḟ D X ↝ X) → ∀ i → μ D i ↝⁻ X i
  foldR' {I} {D} {X} R i (con ds) = mapFoldR D (D at i) R ds >>= (R !!) i

  mapFoldR : {I : Set} (D : Desc I) (E : RDesc I) {X : I → Set} → (Ḟ D X ↝ X) → ⟦ E ⟧ (μ D) ↝⁻ ⟦ E ⟧ X
  mapFoldR D ∎        R _          = any
  mapFoldR D (ṿ i)    R d          = foldR' R i d
  mapFoldR D (σ S E)  R (s , ds)   = map℘ (_,_ s) (mapFoldR D (E s) R ds)
  mapFoldR D (E * E') R (ds , ds') = map℘₂ _,_ (mapFoldR D E R ds) (mapFoldR D E' R ds')

foldR : {I : Set} {D : Desc I} {X : I → Set} → (Ḟ D X ↝ X) → μ D ↝ X
foldR R = wrap (foldR' R)

foldR'-fun-computation : {I : Set} {D : Desc I} {X : I → Set} (f : Ḟ D X ⇉ X) → ∀ {i} (d : μ D i) → foldR' (fun f) i d (fold f d)
foldR'-fun-computation {I} {D} {X} f =
  induction D (λ {i} d → foldR' (fun f) i d (fold f d)) (λ {i} ds all → mapFold D (D at i) f ds , aux (D at i) ds all , refl)
  where
    aux : (D' : RDesc I) (ds : ⟦ D' ⟧ (μ D)) (all : All D' (λ {i} d → foldR' (fun f) i d (fold f d)) ds) →
          mapFoldR D D' (fun f) ds (mapFold D D' f ds)
    aux ∎         ds        all          = tt
    aux (ṿ i)     d         all          = all
    aux (σ S D')  (s , ds)  all          = mapFold D (D' s) f ds , aux (D' s) ds all , refl
    aux (D' * E') (ds , es) (all , all') = mapFold D D' f ds , aux D' ds all , mapFold D E' f es , aux E' es all' , refl

foldR'-fun-unique : {I : Set} {D : Desc I} {X : I → Set} (f : Ḟ D X ⇉ X) → ∀ {i} (d : μ D i) (x : X i) → foldR' (fun f) i d x → fold f d ≡ x
foldR'-fun-unique {I} {D} {X} f =
  induction D (λ {i} d → (x : X i) → foldR' (fun f) i d x → fold f d ≡ x)
              (λ { {i} ds all .(f xs) (xs , mf , refl) → cong f (aux (D at i) ds all xs mf) })
  where
    aux : (D' : RDesc I) (ds : ⟦ D' ⟧ (μ D)) (all : All D' (λ {i} d → (x : X i) → foldR' (fun f) i d x → fold f d ≡ x) ds)
          (xs : ⟦ D' ⟧ X) (mf : mapFoldR D D' (fun f) ds xs) → mapFold D D' f ds ≡ xs
    aux ∎         ds        all          xs        mf                            = refl
    aux (ṿ i)     ds        all          x         mf                            = all x mf
    aux (σ S D')  (s , ds)  all          (.s , xs) (.xs , mf , refl)             = cong (_,_ s) (aux (D' s) ds all xs mf)
    aux (D' * E') (ds , es) (all , all') (xs , ys) (.xs , mf , .ys , mf' , refl) = cong₂ _,_ (aux D' ds all xs mf) (aux E' es all' ys mf')

fun-preserves-fold : {I : Set} (D : Desc I) {X : I → Set} (f : Ḟ D X ⇉ X) → fun (fold f) ≃ foldR {D = D} (fun f)
fun-preserves-fold D f = wrap (λ i → wrap λ { d ._ refl → foldR'-fun-computation f d }) , wrap (λ i → wrap (foldR'-fun-unique f))

foldR-α-lemma : {I : Set} {D : Desc I} {X : I → Set} (R : X ↝ μ D) → foldR α • R ≃ R
foldR-α-lemma {I} {D} {X} R =
  begin
    foldR α • R
      ≃⟨ Setoid.sym setoid (•-cong-r R (fun-preserves-fold D con)) ⟩
    fun (fold con) • R
      ≃⟨ •-cong-r R (fun-cong (λ _ → reflection D)) ⟩
    fun id • R
      ≃⟨ idR-l R ⟩
    R
  □
  where setoid = ≃-Setoid X (μ D)
        open EqReasoning setoid renaming (_≈⟨_⟩_ to _≃⟨_⟩_; _∎ to _□)

foldR-least : {I : Set} (D : Desc I) {X : I → Set} (R : Ḟ D X ↝ X) (S : μ D ↝ X) → R • Ṙ D S • α º ⊆ S → foldR R ⊆ S
foldR-least {I} D {X} R S prefix-point =
  wrap λ _ → wrap (induction D (λ {i} d → (x : X i) → foldR' R i d x → (S !!) i d x)
                               (λ { {i} ds all x (xs , rs , r) →
                                    modus-ponens-⊆ prefix-point i (con ds) x (xs , (ds , refl , aux (D at i) ds all xs rs) , r)}))
  where
    aux : (D' : RDesc I) (ds : ⟦ D' ⟧ (μ D)) (all : All D' (λ {i} d → (x : X i) → foldR' R i d x → (S !!) i d x) ds)
          (xs : ⟦ D' ⟧ X) (rs : mapFoldR D D' R ds xs) → mapR D' S ds xs
    aux ∎         ds        all          xs         rs                             = tt
    aux (ṿ i)     d         all          x          r                              = all x r
    aux (σ T D')  (t , ds)  all          (.t , xs)  (.xs , rs , refl)              = xs , aux (D' t) ds all xs rs , refl
    aux (D' * E') (ds , es) (all , all') (xs , xs') (.xs , rs , .xs' , rs' , refl) = xs , aux D' ds all xs rs , xs' , aux E' es all' xs' rs' , refl

foldR-greatest : {I : Set} (D : Desc I) {X : I → Set} (R : Ḟ D X ↝ X) (S : μ D ↝ X) → S ⊆ R • Ṙ D S • α º → S ⊆ foldR R
foldR-greatest {I} D {X} R S postfix-point = wrap λ _ → wrap (induction D (λ {i} d → (x : X i) → (S !!) i d x → foldR' R i d x) alg)
  where
    aux : (D' : RDesc I) (ds : ⟦ D' ⟧ (μ D)) (all : All D' (λ {i} d → (x : X i) → (S !!) i d x → foldR' R i d x) ds)
          (xs : ⟦ D' ⟧ X) → mapR D' S ds xs → mapFoldR D D' R ds xs
    aux ∎         ds        all          xs         ss                             = tt
    aux (ṿ i)     d         all          x          s                              = all x s
    aux (σ T D')  (t , ds)  all          (.t , xs)  (.xs , ss , refl)              = xs , aux (D' t) ds all xs ss , refl
    aux (D' * E') (ds , es) (all , all') (xs , xs') (.xs , ss , .xs' , ss' , refl) = xs , aux D' ds all xs ss , xs' , aux E' es all' xs' ss' , refl
    alg : {i : I} (ds : Ḟ D (μ D) i) → All (D at i) (λ {i} d → (x : X i) → (S !!) i d x → foldR' R i d x) ds →
          (x : X i) → (S !!) i (con ds) x → foldR' R i (con {D = D} ds) x
    alg {i} ds all x s with modus-ponens-⊆ postfix-point i (con ds) x s
    alg {i} ds all x s | xs , (.ds , refl , ss) , r = xs , aux (D at i) ds all xs ss , r

foldR-computation-⊆ : {I : Set} (D : Desc I) {X : I → Set} (R : Ḟ D X ↝ X) → foldR {D = D} R • α ⊆ R • Ṙ D (foldR R)
foldR-computation-⊆ {I} D {X} R = wrap λ i → wrap λ { ds x (.(con ds) , refl , xs , rs , r) → xs , aux (D at i) ds xs rs , r }
  where
    aux : (D' : RDesc I) (ds : ⟦ D' ⟧ (μ D)) (xs : ⟦ D' ⟧ X) → mapFoldR D D' R ds xs → mapR D' (foldR R) ds xs
    aux ∎         ds        xs         rs                             = tt
    aux (ṿ i)     d         x          r                              = r
    aux (σ S D')  (s , ds)  (.s , xs)  (.xs , rs , refl)              = xs , aux (D' s) ds xs rs , refl
    aux (D' * E') (ds , es) (xs , xs') (.xs , rs , .xs' , rs' , refl) = xs , aux D' ds xs rs , xs' , aux E' es xs' rs' , refl

foldR-computation-⊇ : {I : Set} (D : Desc I) {X : I → Set} (R : Ḟ D X ↝ X) → foldR {D = D} R • α ⊇ R • Ṙ D (foldR R)
foldR-computation-⊇ {I} D {X} R = wrap λ i → wrap λ { ds x (xs , rs , r) → con ds , refl , xs , aux (D at i) ds xs rs , r }
  where
    aux : (D' : RDesc I) (ds : ⟦ D' ⟧ (μ D)) (xs : ⟦ D' ⟧ X) → mapR D' (foldR R) ds xs → mapFoldR D D' R ds xs
    aux ∎         ds        xs         rs                             = tt
    aux (ṿ i)     d         x          r                              = r
    aux (σ S D')  (s , ds)  (.s , xs)  (.xs , rs , refl)              = xs , aux (D' s) ds xs rs , refl
    aux (D' * E') (ds , es) (xs , xs') (.xs , rs , .xs' , rs' , refl) = xs , aux D' ds xs rs , xs' , aux E' es xs' rs' , refl

foldR-computation : {I : Set} (D : Desc I) {X : I → Set} (R : Ḟ D X ↝ X) → foldR {D = D} R • α ≃ R • Ṙ D (foldR R)
foldR-computation D R = foldR-computation-⊆ D R , foldR-computation-⊇ D R

foldR-computation' : {I : Set} (D : Desc I) {X : I → Set} (R : Ḟ D X ↝ X) → foldR {D = D} R ≃ R • Ṙ D (foldR R) • α º
foldR-computation' D {X} R =
  begin
    foldR R
      ≃⟨ Setoid.sym setoid (idR-r (foldR R)) ⟩
    foldR R • idR
      ≃⟨ Setoid.sym setoid (•-cong-l (foldR R) (iso-idR (λ i → Setoid.sym (IsoSetoid Fun) (μ-iso D i)))) ⟩
    foldR R • α • α º
      ≃⟨ ≃-chain-r (foldR R ▪ (α ◇)) (R ▪ (Ṙ D (foldR R) ◇)) (foldR-computation D R) ⟩
    R • Ṙ D (foldR R) • α º
  □
  where setoid = ≃-Setoid (μ D) X
        open EqReasoning setoid renaming (_≈⟨_⟩_ to _≃⟨_⟩_; _∎ to _□)

foldR-fusion-⊇ :
  {I : Set} (D : Desc I) {X Y : I → Set} (R : X ↝ Y) (S : Ḟ D X ↝ X) (T : Ḟ D Y ↝ Y) → R • S ⊇ T • Ṙ D R → R • foldR {D = D} S ⊇ foldR T
foldR-fusion-⊇ D {X} {Y} R S T fusion-condition =
  foldR-least D T (R • foldR S)
    (begin
       R • foldR S
         ⊇⟨ •-monotonic-l R (proj₁ (idR-r (foldR S))) ⟩
       R • foldR S • idR
         ⊇⟨ ⊇-chain-l (R ▪ foldR S ◇) (proj₁ (iso-idR (λ i → Relation.Binary.Setoid.sym (IsoSetoid Fun) (μ-iso D i)))) ⟩
       R • foldR S • α • α º
         ⊇⟨ ⊇-chain (R ◇) (foldR S ▪ α ◇) (S ▪ Ṙ D (foldR S) ◇) (proj₂ (foldR-computation D S)) ⟩
       R • S • Ṙ D (foldR S) • α º
         ⊇⟨ ⊇-chain-r (R ▪ S ◇) (T ▪ Ṙ D R ◇) fusion-condition ⟩
       T • Ṙ D R • Ṙ D (foldR S) • α º
         ⊇⟨ ⊇-chain (T ◇) (Ṙ D R ▪ Ṙ D (foldR S) ◇) (Ṙ D (R • foldR S) ◇) (proj₁ (Ṙ-preserves-comp D R (foldR S))) ⟩
       T • Ṙ D (R • foldR S) • α º
     □)
  where open PreorderReasoning (⊇-Preorder (μ D) Y) renaming (_∼⟨_⟩_ to _⊇⟨_⟩_; _∎ to _□)

foldR-fusion-⊆ :
  {I : Set} (D : Desc I) {X Y : I → Set} (R : X ↝ Y) (S : Ḟ D X ↝ X) (T : Ḟ D Y ↝ Y) → R • S ⊆ T • Ṙ D R → R • foldR {D = D} S ⊆ foldR T
foldR-fusion-⊆ D {X} {Y} R S T fusion-condition =
  foldR-greatest D T (R • foldR S)
    (begin
       R • foldR S
         ⊆⟨ •-monotonic-l R (proj₂ (idR-r (foldR S))) ⟩
       R • foldR S • idR
         ⊆⟨ ⊆-chain-l (R ▪ foldR S ◇) (proj₂ (iso-idR (λ i → Relation.Binary.Setoid.sym (IsoSetoid Fun) (μ-iso D i)))) ⟩
       R • foldR S • α • α º
         ⊆⟨ ⊆-chain (R ◇) (foldR S ▪ α ◇) (S ▪ Ṙ D (foldR S) ◇) (proj₁ (foldR-computation D S)) ⟩
       R • S • Ṙ D (foldR S) • α º
         ⊆⟨ ⊆-chain-r (R ▪ S ◇) (T ▪ Ṙ D R ◇) fusion-condition ⟩
       T • Ṙ D R • Ṙ D (foldR S) • α º
         ⊆⟨ ⊆-chain (T ◇) (Ṙ D R ▪ Ṙ D (foldR S) ◇) (Ṙ D (R • foldR S) ◇) (proj₂ (Ṙ-preserves-comp D R (foldR S))) ⟩
       T • Ṙ D (R • foldR S) • α º
     □)
  where open PreorderReasoning (⊆-Preorder (μ D) Y) renaming (_∼⟨_⟩_ to _⊆⟨_⟩_; _∎ to _□)

foldR-fusion :
  {I : Set} (D : Desc I) {X Y : I → Set} (R : X ↝ Y) (S : Ḟ D X ↝ X) (T : Ḟ D Y ↝ Y) → R • S ≃ T • Ṙ D R → R • foldR {D = D} S ≃ foldR T
foldR-fusion D R S T (fusion-condition-⊆ , fusion-condition-⊇) =
  foldR-fusion-⊆ D R S T fusion-condition-⊆ , foldR-fusion-⊇ D R S T fusion-condition-⊇
