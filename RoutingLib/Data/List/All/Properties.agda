open import Data.Bool using (Bool; true; if_then_else_)
open import Data.List using (List; []; _∷_; _++_; filter; concat; foldr; gfilter; map) --renaming (map to mapₗ)
open import Data.List.All using (All; []; _∷_) renaming (map to mapₐ)
open import Data.List.All.Properties
open import Data.List.Any using (Any; here; there)
open import Data.Maybe using (Maybe; just; nothing; Eq; drop-just)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Unary using (Decidable; _⊆_)
open import Relation.Binary using (Rel; _Preserves_⟶_; _Respects_; Setoid)
open import Relation.Binary.PropositionalEquality using (_≡_; inspect; [_]; subst₂) renaming (sym to ≡-sym; trans to ≡-trans)
open import Data.Empty using (⊥-elim)
open import Data.Product using (proj₁; proj₂)
open import Function using (_∘_)
open import Function.Surjection hiding (_∘_)
open import Algebra.FunctionProperties.Core using (Op₂)
open import Relation.Unary using () renaming (_⊆_ to _⋐_)

open import RoutingLib.Data.List.All
open import RoutingLib.Data.List using (allFin; combine)
open import RoutingLib.Data.Maybe.Properties using () renaming (trans to eq-trans)

module RoutingLib.Data.List.All.Properties where

  forced-map : ∀ {a b p} {A : Set a} {B : Set b} {P : B → Set p} {f : A → B} → (∀ v → P (f v)) → (xs : List A) → All P (map f xs)
  forced-map Pf []       = []
  forced-map Pf (x ∷ xs) = Pf x ∷ forced-map Pf xs

  gfilter-all : ∀ {a b p q} {A : Set a} {B : Set b} {P : A → Set p} {Q : B → Set q} {f : A → Maybe B} → (∀ {x} → P x → ∀ {y} → f x ≡ just y → Q y) → All P ⋐ All Q ∘ gfilter f
  gfilter-all _ [] = []
  gfilter-all {f = f} f-inj {x ∷ xs} (px ∷ pxs) with f x | inspect f x
  ... | nothing | _            = gfilter-all f-inj pxs
  ... | just v  | [ fₓ≡justᵥ ] = f-inj px fₓ≡justᵥ ∷ gfilter-all f-inj pxs

  -- Forcing and preserves

  map-preserves-predicates : ∀ {a b p} {A : Set a} {B : Set b} {P : B → Set p} {f : A → B} → (∀ x → P (f x)) → (xs : List A) → All P (map f xs)
  map-preserves-predicates _   []       = []
  map-preserves-predicates pfx (x ∷ xs) = pfx x ∷ map-preserves-predicates pfx xs












  ----------------------
  -- Pushed to stdlib --
  ----------------------

  ++-all : ∀ {a p} {A : Set a} {P : A → Set p} {xs ys} → All P xs → All P ys → All P (xs ++ ys)
  ++-all []         pys = pys
  ++-all (px ∷ pxs) pys = px ∷ ++-all pxs pys

  ¬All→Any¬ : ∀ {a p} {A : Set a} {P : A → Set p} {xs} → Decidable P → ¬ (All P xs) → Any (¬_ ∘ P) xs
  ¬All→Any¬ {xs = []}     dec ¬∀ = ⊥-elim (¬∀ [])
  ¬All→Any¬ {xs = x ∷ xs} dec ¬∀ with dec x
  ... | yes p = there (¬All→Any¬ dec (¬∀ ∘ _∷_ p))
  ... | no ¬p = here ¬p

  ¬Any→All¬ : ∀ {a p} {A : Set a} {P : A → Set p} {xs} → ¬ (Any P xs) → All (¬_ ∘ P) xs
  ¬Any→All¬ {xs = []} ¬p = []
  ¬Any→All¬ {xs = x ∷ xs} ¬p = (¬p ∘ here) ∷ ¬Any→All¬ (¬p ∘ there)

  All¬→¬Any : ∀ {a p} {A : Set a} {P : A → Set p} {xs} → All (¬_ ∘ P) xs → ¬ (Any P xs)
  All¬→¬Any []        ()
  All¬→¬Any (¬p ∷ _)  (here  p) = ¬p p
  All¬→¬Any (_  ∷ ¬p) (there p) = All¬→¬Any ¬p p

  -----------------------
  -- To push to stdlib --
  -----------------------

  concat-all : ∀ {a p} {A : Set a} {P : A → Set p} {xss : List (List A)}
               → All (All P) xss → All P (concat xss)
  concat-all []           = []
  concat-all (pxs ∷ pxss) = ++-all pxs (concat-all pxss)



  -----------
  -- Other --
  -----------

  -- All pairs

  module SetoidProperties {a ℓ} (S : Setoid a ℓ) where

    open Setoid S renaming (Carrier to A)
    open Data.List.Any.Membership S using (_∈_)

    ∈-All : ∀ {p} {P : A → Set p} xs → (∀ {v} → v ∈ xs → P v) → All P xs
    ∈-All [] _ = []
    ∈-All (x ∷ xs) ∈⇨P = ∈⇨P (here refl) ∷ ∈-All xs (∈⇨P ∘ there)

    All-∈ : ∀ {p} {P : A → Set p} → P Respects _≈_ → ∀ {v xs} → All P xs → v ∈ xs → P v
    All-∈ resp (px ∷ pxs) (here v≈x)   = resp (sym v≈x) px
    All-∈ resp (px ∷ pxs) (there v∈xs) = All-∈ resp pxs v∈xs

    map-all : ∀ {b p} {B : Set b} {P : B → Set p} f {xs : List A} → (∀ {x} → x ∈ xs → P (f x)) → All P (map f xs)
    map-all f {[]}     pres = []
    map-all f {x ∷ xs} pres = pres (here refl) ∷ map-all f (pres ∘ there)

  open SetoidProperties public



  module DoubleSetoidProperties
    {a₁ ℓ₁} (S₁ : Setoid a₁ ℓ₁)
    {a₂ ℓ₂} (S₂ : Setoid a₂ ℓ₂) where

    open Setoid S₁ renaming (Carrier to A₁; refl to refl₁)
    open Setoid S₂ renaming (Carrier to A₂)

    open Data.List.Any.Membership S₁ using () renaming (_∈_ to _∈₁_)
    open Data.List.Any.Membership S₂ using () renaming (_∈_ to _∈₂_)

    combine-all : ∀ {b p} {B : Set b} {P : B → Set p} _•_ (xs : List A₁) (ys : List A₂) → (∀ {x y} → x ∈₁ xs → y ∈₂ ys → P (x • y)) → All P (combine _•_ xs ys)
    combine-all _•_ []       ys pres = []
    combine-all _•_ (x ∷ xs) ys pres = ++-all (map-all S₂ (x •_) (pres (here refl₁))) (combine-all _•_ xs ys (pres ∘ there))

  open DoubleSetoidProperties public



  map-pairs : ∀ {a b ℓ₁ ℓ₂} {A : Set a} {B : Set b}  {_~₁_ : Rel A ℓ₁} {_~₂_ : Rel B ℓ₂}
              {f : A → B} → f Preserves _~₁_ ⟶ _~₂_ → AllPairs _~₁_ ⋐ AllPairs _~₂_ ∘ map f
  map-pairs f-pres []           = []
  map-pairs f-pres (x∉xs ∷ xs!) = All-map (mapₐ f-pres x∉xs) ∷ map-pairs f-pres xs!


  gfilter-pairs : ∀ {a b ℓ₁ ℓ₂} {A : Set a} {B : Set b} {_~₁_ : Rel A ℓ₁} {_~₂_ : Rel B ℓ₂}
                  (f : A → Maybe B) → (∀ {x y} → x ~₁ y → (f x ≡ nothing) ⊎ (f y ≡ nothing) ⊎ (Eq _~₂_ (f x) (f y)))
                  → AllPairs _~₁_ ⋐ AllPairs _~₂_ ∘ gfilter f
  gfilter-pairs _ _ [] = []
  gfilter-pairs {_~₁_ = _~₁_} {_~₂_} f f-inj {x ∷ xs} (px ∷ pxs) with f x | inspect f x
  ... | nothing | _            = gfilter-pairs f f-inj pxs
  ... | just v  | [ fx≡justv ] = gfilter-all convert px ∷ gfilter-pairs f f-inj pxs
    where
    convert : ∀ {a} → x ~₁ a → ∀ {b} → f a ≡ just b → v ~₂ b
    convert {a} x~a {b} fa≡justb with f-inj x~a
    ... | inj₁ fx≡nothing        = contradiction (≡-trans (≡-sym fx≡nothing) fx≡justv) λ()
    ... | inj₂ (inj₁ fa≡nothing) = contradiction (≡-trans (≡-sym fa≡nothing) fa≡justb) λ()
    ... | inj₂ (inj₂ fx~fa)      = drop-just (subst₂ (Eq _~₂_) fx≡justv fa≡justb fx~fa)

{-
  filter-all : ∀ {a} {A : Set a} (P : A → Bool) → (xs : List A) → All (λ v → P v ≡ true) (filter P xs)
  filter-all P [] = []
  filter-all {A = A} P (x ∷ xs) = result

    where

    filter-lift : A → Maybe A
    filter-lift x = if P x then just x else nothing

    result : All (λ v → P v ≡ true) (filter P (x ∷ xs))
    result with filter-lift x
    ... | nothing = filter-all P xs
    ... | just t = {!!} ∷ filter-all P xs
-}

