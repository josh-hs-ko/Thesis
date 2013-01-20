module Thesis.Relation.Fold where

open import Thesis.Prelude.Function.Fam
open import Thesis.Description
open import Thesis.Relation

open import Function using (id)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; _×_)
open import Relation.Binary using (Setoid)
import Relation.Binary.EqReasoning as EqReasoning
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; subst)


foldR-fun-⊑ : {I : Set} {D : Desc I} {X : I → Set} (f : Ḟ D X ⇒ X) → ∀ {i} (d : μ D i) → foldR' (fun f) d (fold f d)
foldR-fun-⊑ {I} {D} {X} f =
  induction D (λ d → foldR' (fun f) d (fold f d)) (λ {i} ds all → mapFold D (D at i) f ds , aux (D at i) ds all , refl)
  where
    aux : (D' : RDesc I) (ds : ⟦ D' ⟧ (μ D)) (all : All D' (λ d → foldR' (fun f) d (fold f d)) ds) → mapFoldR D D' (fun f) ds (mapFold D D' f ds)
    aux ∎         ds        all          = tt
    aux (ṿ i)     d         all          = all
    aux (σ S D')  (s , ds)  all          = mapFold D (D' s) f ds , aux (D' s) ds all , refl
    aux (D' * E') (ds , es) (all , all') = mapFold D D' f ds , aux D' ds all , mapFold D E' f es , aux E' es all' , refl

foldR-fun-⊒ : {I : Set} {D : Desc I} {X : I → Set} (f : Ḟ D X ⇒ X) → ∀ {i} (d : μ D i) (x : X i) → foldR' (fun f) d x → fold f d ≡ x
foldR-fun-⊒ {I} {D} {X} f =
  induction D (λ {i} d → (x : X i) → foldR' (fun f) d x → fold f d ≡ x)
              (λ { {i} ds all .(f xs) (xs , mf , refl) → cong f (aux (D at i) ds all xs mf) })
  where
    aux : (D' : RDesc I) (ds : ⟦ D' ⟧ (μ D)) (all : All D' (λ {i} d → (x : X i) → foldR' (fun f) d x → fold f d ≡ x) ds)
          (xs : ⟦ D' ⟧ X) (mf : mapFoldR D D' (fun f) ds xs) → mapFold D D' f ds ≡ xs
    aux ∎         ds        all          xs        mf                            = refl
    aux (ṿ i)     ds        all          x         mf                            = all x mf
    aux (σ S D')  (s , ds)  all          (.s , xs) (.xs , mf , refl)             = cong (_,_ s) (aux (D' s) ds all xs mf)
    aux (D' * E') (ds , es) (all , all') (xs , ys) (.xs , mf , .ys , mf' , refl) = cong₂ _,_ (aux D' ds all xs mf) (aux E' es all' ys mf')

fun-preserves-fold : {I : Set} (D : Desc I) {X : I → Set} (f : Ḟ D X ⇒ X) → fun (fold f) ≃ foldR {D = D} (fun f)
fun-preserves-fold D f = wrap (λ d → wrap λ {._ refl → foldR-fun-⊑ f d }) , wrap (λ d → wrap (foldR-fun-⊒ f d))

foldR-con-lemma : {I : Set} {D : Desc I} {X : I → Set} (R : X ↝ μ D) → foldR (fun con) • R ≃ R
foldR-con-lemma {I} {D} {X} R =
  begin
    foldR (fun con) • R
      ≃⟨ Setoid.sym (≃-Setoid X (μ D)) (•-cong-r R (fun-preserves-fold D con)) ⟩
    fun (fold con) • R
      ≃⟨ •-cong-r R (fun-cong (reflection D)) ⟩
    fun id • R
      ≃⟨ idR-l R ⟩
    R
  □
  where open EqReasoning (≃-Setoid X (μ D)) renaming (_≈⟨_⟩_ to _≃⟨_⟩_; _∎ to _□)

foldR-least : {I : Set} (D : Desc I) {X : I → Set} (R : Ḟ D X ↝ X) (S : μ D ↝ X) → R • Ṙ D S • (fun con)º ⊆ S → foldR R ⊆ S
foldR-least {I} D {X} R S prefix-point =
  wrap λ d → wrap (induction D (λ {i} d → (x : X i) → foldR' R d x → Λ S d x)
                               (λ { {i} ds all x (xs , rs , r) →
                                    modus-ponens-⊆ prefix-point (con ds) x (xs , (ds , refl , aux (D at i) ds all xs rs) , r)}) d)
  where
    aux : (D' : RDesc I) (ds : ⟦ D' ⟧ (μ D)) (all : All D' (λ {i} d → (x : X i) → foldR' R d x → Λ S d x) ds)
          (xs : ⟦ D' ⟧ X) (rs : mapFoldR D D' R ds xs) → mapR D' S ds xs
    aux ∎         ds        all          xs         rs                             = tt
    aux (ṿ i)     d         all          x          r                              = all x r
    aux (σ T D')  (t , ds)  all          (.t , xs)  (.xs , rs , refl)              = xs , aux (D' t) ds all xs rs , refl
    aux (D' * E') (ds , es) (all , all') (xs , xs') (.xs , rs , .xs' , rs' , refl) = xs , aux D' ds all xs rs , xs' , aux E' es all' xs' rs' , refl

foldR-greatest : {I : Set} (D : Desc I) {X : I → Set} (R : Ḟ D X ↝ X) (S : μ D ↝ X) → S ⊆ R • Ṙ D S • (fun con)º → S ⊆ foldR R
foldR-greatest {I} D {X} R S postfix-point =
  wrap λ { {i} d → wrap λ x s → induction D (λ {i} d → (x : X i) → Λ S d x → foldR' R d x) alg d x s }
  where
    aux : (D' : RDesc I) (ds : ⟦ D' ⟧ (μ D)) (all : All D' (λ {i} d → (x : X i) → Λ S d x → foldR' R d x) ds)
          (xs : ⟦ D' ⟧ X) → mapR D' S ds xs → mapFoldR D D' R ds xs
    aux ∎         ds        all          xs         ss                             = tt
    aux (ṿ i)     d         all          x          s                              = all x s
    aux (σ T D')  (t , ds)  all          (.t , xs)  (.xs , ss , refl)              = xs , aux (D' t) ds all xs ss , refl
    aux (D' * E') (ds , es) (all , all') (xs , xs') (.xs , ss , .xs' , ss' , refl) = xs , aux D' ds all xs ss , xs' , aux E' es all' xs' ss' , refl
    alg : {i : I} (ds : Ḟ D (μ D) i) → All (D at i) (λ {i} d → (x : X i) → Λ S d x → foldR' R d x) ds →
          (x : X i) → Λ S (con ds) x → foldR' R (con {D = D} ds) x
    alg {i} ds all x s with modus-ponens-⊆ postfix-point (con ds) x s
    alg {i} ds all x s | xs , (.ds , refl , ss) , r = xs , aux (D at i) ds all xs ss , r

foldR-computation-⊆ : {I : Set} (D : Desc I) {X : I → Set} (R : Ḟ D X ↝ X) → foldR {D = D} R • fun con ⊆ R • Ṙ D (foldR R)
foldR-computation-⊆ {I} D {X} R = wrap λ {i} ds → wrap λ { x (.(con ds) , refl , xs , rs , r) → xs , aux (D at i) ds xs rs , r }
  where
    aux : (D' : RDesc I) (ds : ⟦ D' ⟧ (μ D)) (xs : ⟦ D' ⟧ X) → mapFoldR D D' R ds xs → mapR D' (foldR R) ds xs
    aux ∎         ds        xs         rs                             = tt
    aux (ṿ i)     d         x          r                              = r
    aux (σ S D')  (s , ds)  (.s , xs)  (.xs , rs , refl)              = xs , aux (D' s) ds xs rs , refl
    aux (D' * E') (ds , es) (xs , xs') (.xs , rs , .xs' , rs' , refl) = xs , aux D' ds xs rs , xs' , aux E' es xs' rs' , refl

foldR-computation-⊇ : {I : Set} (D : Desc I) {X : I → Set} (R : Ḟ D X ↝ X) → foldR {D = D} R • fun con ⊇ R • Ṙ D (foldR R)
foldR-computation-⊇ {I} D {X} R = wrap λ {i} ds → wrap λ { x (xs , rs , r) → con ds , refl , xs , aux (D at i) ds xs rs , r }
  where
    aux : (D' : RDesc I) (ds : ⟦ D' ⟧ (μ D)) (xs : ⟦ D' ⟧ X) → mapR D' (foldR R) ds xs → mapFoldR D D' R ds xs
    aux ∎         ds        xs         rs                             = tt
    aux (ṿ i)     d         x          r                              = r
    aux (σ S D')  (s , ds)  (.s , xs)  (.xs , rs , refl)              = xs , aux (D' s) ds xs rs , refl
    aux (D' * E') (ds , es) (xs , xs') (.xs , rs , .xs' , rs' , refl) = xs , aux D' ds xs rs , xs' , aux E' es xs' rs' , refl

foldR-computation : {I : Set} (D : Desc I) {X : I → Set} (R : Ḟ D X ↝ X) → foldR {D = D} R • fun con ≃ R • Ṙ D (foldR R)
foldR-computation D R = foldR-computation-⊆ D R , foldR-computation-⊇ D R