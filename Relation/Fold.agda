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
open import Data.Product using (Σ; Σ-syntax; _,_; proj₁; proj₂; _×_)
open import Data.List using (List; []; _∷_)
open import Relation.Binary using (module Setoid)
import Relation.Binary.EqReasoning as EqReasoning
import Relation.Binary.PreorderReasoning as PreorderReasoning
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; subst)


mutual

  foldR' : {I : Set} {D : Desc I} {X : I → Set} → (Ḟ D X ↝ X) → ∀ i → μ D i ↝⁻ X i
  foldR' {I} {D} {X} R i (con ds) = mapFoldR D (Desc.comp D i) R ds >>= (R !!) i

  mapFoldR : {I : Set} (D : Desc I) (E : RDesc I) {X : I → Set} → (Ḟ D X ↝ X) → ⟦ E ⟧ (μ D) ↝⁻ ⟦ E ⟧ X
  mapFoldR D (ṿ is)   R ds       = mapFoldR-Ṗ D R is ds
  mapFoldR D (σ S E)  R (s , ds) = map℘ (_,_ s) (mapFoldR D (E s) R ds)

  mapFoldR-Ṗ : {I : Set} (D : Desc I) {X : I → Set} → (Ḟ D X ↝ X) → (is : List I) → Ṗ is (μ D) ↝⁻ Ṗ is X
  mapFoldR-Ṗ D R []       _        = any
  mapFoldR-Ṗ D R (i ∷ is) (d , ds) = map℘₂ _,_ (foldR' R i d) (mapFoldR-Ṗ D R is ds)

foldR : {I : Set} {D : Desc I} {X : I → Set} → (Ḟ D X ↝ X) → μ D ↝ X
foldR R = wrap (foldR' R)

foldR'-fun-computation : {I : Set} {D : Desc I} {X : I → Set} (f : Ḟ D X ⇉ X) → ∀ {i} (d : μ D i) → foldR' (fun f) i d (fold f d)
foldR'-fun-computation {I} {D} {X} f =
  induction D (λ i d → foldR' (fun f) i d (fold f d)) (λ i ds ihs → mapFold D (Desc.comp D i) f ds , aux (Desc.comp D i) ds ihs , refl)
  where
    aux : (D' : RDesc I) (ds : ⟦ D' ⟧ (μ D)) → All D' (λ i d → foldR' (fun f) i d (fold f d)) ds →
          mapFoldR D D' (fun f) ds (mapFold D D' f ds)
    aux (ṿ [])       _        _          = tt
    aux (ṿ (i ∷ is)) (d , ds) (ih , ihs) = fold f d , ih , mapFold-Ṗ D f is ds , aux (ṿ is) ds ihs , refl
    aux (σ S D')     (s , ds) ihs        = mapFold D (D' s) f ds , aux (D' s) ds ihs , refl

foldR'-fun-unique : {I : Set} {D : Desc I} {X : I → Set} (f : Ḟ D X ⇉ X) → ∀ {i} (d : μ D i) (x : X i) → foldR' (fun f) i d x → fold f d ≡ x
foldR'-fun-unique {I} {D} {X} f =
  induction D (λ i d → (x : X i) → foldR' (fun f) i d x → fold f d ≡ x)
              (λ { i ds ihs .(f xs) (xs , mf , refl) → cong f (aux (Desc.comp D i) ds ihs xs mf) })
  where
    aux : (D' : RDesc I) (ds : ⟦ D' ⟧ (μ D)) → All D' (λ i d → (x : X i) → foldR' (fun f) i d x → fold f d ≡ x) ds →
          (xs : ⟦ D' ⟧ X) → mapFoldR D D' (fun f) ds xs → mapFold D D' f ds ≡ xs
    aux (ṿ [])       _        _          _         _                         = refl
    aux (ṿ (i ∷ is)) (d , ds) (ih , ihs) (x , xs)  (._ , r , ._ , rs , refl) = cong₂ _,_ (ih x r) (aux (ṿ is) ds ihs xs rs)
    aux (σ S D')     (s , ds) ihs        (.s , xs) (.xs , eqs , refl)        = cong (_,_ s) (aux (D' s) ds ihs xs eqs)

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
  wrap λ _ → wrap (induction D (λ i d → (x : X i) → foldR' R i d x → (S !!) i d x)
                               (λ { i ds ihs x (xs , rs , r) →
                                    modus-ponens-⊆ prefix-point i (con ds) x (xs , (ds , refl , aux (Desc.comp D i) ds ihs xs rs) , r)}))
  where
    aux : (D' : RDesc I) (ds : ⟦ D' ⟧ (μ D)) (ihs : All D' (λ i d → (x : X i) → foldR' R i d x → (S !!) i d x) ds)
          (xs : ⟦ D' ⟧ X) (rs : mapFoldR D D' R ds xs) → mapR D' S ds xs
    aux (ṿ [])       _        _          _         _                         = tt
    aux (ṿ (i ∷ is)) (d , ds) (ih , ihs) (x , xs)  (._ , r , ._ , rs , refl) = x , ih x r , xs , aux (ṿ is) ds ihs xs rs , refl
    aux (σ T D')     (t , ds) ihs        (.t , xs) (.xs , rs , refl)         = xs , aux (D' t) ds ihs xs rs , refl

foldR-greatest : {I : Set} (D : Desc I) {X : I → Set} (R : Ḟ D X ↝ X) (S : μ D ↝ X) → S ⊆ R • Ṙ D S • α º → S ⊆ foldR R
foldR-greatest {I} D {X} R S postfix-point = wrap λ _ → wrap (induction D (λ i d → (x : X i) → (S !!) i d x → foldR' R i d x) alg)
  where
    aux : (D' : RDesc I) (ds : ⟦ D' ⟧ (μ D)) → All D' (λ i d → (x : X i) → (S !!) i d x → foldR' R i d x) ds →
          (xs : ⟦ D' ⟧ X) → mapR D' S ds xs → mapFoldR D D' R ds xs
    aux (ṿ [])       _        _          _         _                         = tt
    aux (ṿ (i ∷ is)) (d , ds) (ih , ihs) (x , xs)  (._ , s , ._ , ss , refl) = x , ih x s , xs , aux (ṿ is) ds ihs xs ss , refl
    aux (σ T D')     (t , ds) ihs        (.t , xs) (.xs , ss , refl)         = xs , aux (D' t) ds ihs xs ss , refl
    alg : (i : I) (ds : Ḟ D (μ D) i) → All (Desc.comp D i) (λ i d → (x : X i) → (S !!) i d x → foldR' R i d x) ds →
          (x : X i) → (S !!) i (con ds) x → foldR' R i (con {D = D} ds) x
    alg i ds ihs x s with modus-ponens-⊆ postfix-point i (con ds) x s
    alg i ds ihs x s | xs , (.ds , refl , ss) , r = xs , aux (Desc.comp D i) ds ihs xs ss , r

foldR-computation-⊆ : {I : Set} (D : Desc I) {X : I → Set} (R : Ḟ D X ↝ X) → foldR {D = D} R • α ⊆ R • Ṙ D (foldR R)
foldR-computation-⊆ {I} D {X} R = wrap λ i → wrap λ { ds x (.(con ds) , refl , xs , rs , r) → xs , aux (Desc.comp D i) ds xs rs , r }
  where
    aux : (D' : RDesc I) (ds : ⟦ D' ⟧ (μ D)) (xs : ⟦ D' ⟧ X) → mapFoldR D D' R ds xs → mapR D' (foldR R) ds xs
    aux (ṿ [])       _        _         _                         = tt
    aux (ṿ (i ∷ is)) (d , ds) (x , xs)  (._ , r , ._ , rs , refl) = x , r , xs , aux (ṿ is) ds xs rs , refl
    aux (σ S D')     (s , ds) (.s , xs) (.xs , rs , refl)         = xs , aux (D' s) ds xs rs , refl

foldR-computation-⊇ : {I : Set} (D : Desc I) {X : I → Set} (R : Ḟ D X ↝ X) → foldR {D = D} R • α ⊇ R • Ṙ D (foldR R)
foldR-computation-⊇ {I} D {X} R = wrap λ i → wrap λ { ds x (xs , rs , r) → con ds , refl , xs , aux (Desc.comp D i) ds xs rs , r }
  where
    aux : (D' : RDesc I) (ds : ⟦ D' ⟧ (μ D)) (xs : ⟦ D' ⟧ X) → mapR D' (foldR R) ds xs → mapFoldR D D' R ds xs
    aux (ṿ [])       _        _         _                         = tt
    aux (ṿ (i ∷ is)) (d , ds) (x , xs)  (._ , r , ._ , rs , refl) = x , r , xs , aux (ṿ is) ds xs rs , refl
    aux (σ S D')     (s , ds) (.s , xs) (.xs , rs , refl)         = xs , aux (D' s) ds xs rs , refl

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
