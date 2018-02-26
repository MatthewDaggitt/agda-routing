open import Data.Nat using (ℕ; zero; suc; s≤s; _+_)
open import Data.Fin using (Fin; _<_; _≤_; inject₁) renaming (zero to fzero; suc to fsuc)
open import Algebra.FunctionProperties using (Op₂)
open import Data.Vec hiding (map; zipWith)
open import Data.Product using (∃; ∃₂; _,_; _×_) renaming (map to mapₚ)
open import Data.List using ([]; _∷_)
open import Data.List.Any as Any using (here; there)
open import Data.List.Any.Membership.Propositional using () renaming (_∈_ to _∈ₗ_)
open import Function using (_∘_; id)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary using (Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym)

open import RoutingLib.Data.Vec
open import RoutingLib.Algebra.FunctionProperties using (_×-Preserves_)

module RoutingLib.Data.Vec.Properties where

  -----------------------
  -- To push to stdlib --
  -----------------------

  ∈-lookup : ∀ {a n} {A : Set a} {v : A} {xs : Vec A n} → v ∈ xs → ∃ λ i → lookup i xs ≡ v
  ∈-lookup here = fzero , refl
  ∈-lookup (there v∈xs) = mapₚ fsuc id (∈-lookup v∈xs)

  ∈-lookup⁺ : ∀ {a n} {A : Set a} i (xs : Vec A n) → lookup i xs ∈ xs
  ∈-lookup⁺ fzero    (x ∷ xs) = here
  ∈-lookup⁺ (fsuc i) (x ∷ xs) = there (∈-lookup⁺ i xs)

  ∈-fromList⁻ : ∀ {a} {A : Set a} {v : A} {xs} → v ∈ fromList xs → v ∈ₗ xs
  ∈-fromList⁻ {xs = []}    ()
  ∈-fromList⁻ {xs = _ ∷ _} here         = here refl
  ∈-fromList⁻ {xs = _ ∷ _} (there v∈xs) = there (∈-fromList⁻ v∈xs)

  {-
  ∈-toList⁺ : ∀ {a n} {A : Set a} {xs : Vec A n} {v}  → v ∈ xs → v ∈ₗ toList xs
  ∈-toList⁺ hereᵥ         = here (reflexive refl)
  ∈-toList⁺ (thereᵥ v∈xs) = there (∈-toList⁺ v∈xs)
  -}
{-
{-
  ∈-toList : ∀ {a n} {A : Set a} {v : A} {xs : Vec A n} → v ∈ₗ (toList xs) → v ∈ xs
  ∈-toList {xs = []}     ()
  ∈-toList {xs = x ∷ xs} (here refl)  = here
  ∈-toList {xs = x ∷ xs} (there v∈xs) = there (∈-toList v∈xs)
-}

  lookup-map : ∀ {a b n} {A : Set a} {B : Set b} {f : A → B} (i : Fin n) (xs : Vec A n) → lookup i (map f xs) ≡ f (lookup i xs)
  lookup-map fzero (x ∷ xs) = refl
  lookup-map (fsuc i) (x ∷ xs) = lookup-map i xs

  lookup-zipWith : ∀ {a n} {A : Set a} (_•_ : Op₂ A) (i : Fin n) (xs ys : Vec A n) → lookup i (zipWith _•_ xs ys) ≡ (lookup i xs) • (lookup i ys)
  lookup-zipWith _ fzero  (x ∷ _)  (y ∷ _)    = refl
  lookup-zipWith _•_ (fsuc i) (_ ∷ xs) (_ ∷ ys)  = lookup-zipWith _•_ i xs ys

  lookup-∈ : ∀ {a n} {A : Set a} {v : A} {xs : Vec A n} {i : Fin n} → lookup i xs ≡ v → v ∈ xs
  lookup-∈ {xs = []} {i = ()}
  lookup-∈ {xs = x ∷ xs} {i = fzero} refl = here
  lookup-∈ {xs = x ∷ xs} {i = fsuc i} xsᵢ≡v = there (lookup-∈ {i = i} xsᵢ≡v)

  ----------------------
  -- Pushed to stdlib --
  ----------------------

  v[i]=x⇨lookup[i,v]≡x : ∀ {a n} {S : Set a} {x : S} {v : Vec S n} {i : Fin n}  → v [ i ]= x → lookup i v ≡ x
  v[i]=x⇨lookup[i,v]≡x here = refl
  v[i]=x⇨lookup[i,v]≡x (there xs[i]=x) = v[i]=x⇨lookup[i,v]≡x xs[i]=x


  ----------
  -- Rest --
  ----------

  map-∃-∈ : ∀ {a b n} {A : Set a} {B : Set b} {f : A → B} {v : B} (xs : Vec A n) → v ∈ map f xs → ∃ λ y → y ∈ xs × v ≡ f y
  map-∃-∈ []       ()
  map-∃-∈ (x ∷ xs) here = x , here , refl
  map-∃-∈ (x ∷ xs) (there v∈mapfxs) with map-∃-∈ xs v∈mapfxs
  ... | y , y∈xs , v≈fy = y , there y∈xs , v≈fy

  foldr-pres-P : ∀ {a p} {A : Set a} (P : A → Set p) (_⊕_ : Op₂ A) → _⊕_ ×-Preserves P → ∀ {n e} (xs : Vec A n) → (∀ i → P (lookup i xs)) → P e → P (foldr (λ _ → A) _⊕_ e xs)
  foldr-pres-P P _⊕_ ⊕-pres-p []       Pxs Pe = Pe
  foldr-pres-P P _⊕_ ⊕-pres-p (x ∷ xs) Pxs Pe = ⊕-pres-p (Pxs fzero) (foldr-pres-P P _⊕_ ⊕-pres-p xs (Pxs ∘ fsuc) Pe)

  foldr₁-pres-P : ∀ {a p} {A : Set a} (P : A → Set p) (_⊕_ : Op₂ A) → _⊕_ ×-Preserves P → ∀ {n} (xs : Vec A (suc n)) → (∀ i → P (lookup i xs)) → P (foldr₁ _⊕_ xs)
  foldr₁-pres-P _ _   _        (x ∷ [])     P-holds  = P-holds fzero
  foldr₁-pres-P P _⊕_ ⊕-pres-P (x ∷ y ∷ xs) P-holds  = ⊕-pres-P (P-holds fzero) (foldr₁-pres-P P _⊕_ ⊕-pres-P (y ∷ xs) (P-holds ∘ fsuc))

{-
  ∉⇒List-∉ : ∀ {a} {A : Set a} {n x} {xs : Vec A n} → x ∉ xs → x ∉ₗ toList xs
  ∉⇒List-∉ {xs = []} _ ()
  ∉⇒List-∉ {xs = x ∷ xs} x∉x∷xs (here refl) = x∉x∷xs here
  ∉⇒List-∉ {xs = x ∷ xs} x∉x∷xs (there x∈xsₗ) = ∉⇒List-∉ (λ x∈xs → x∉x∷xs (there x∈xs)) x∈xsₗ
-}

  0∉map-fsuc : ∀ {n m} (xs : Vec (Fin m) n) → fzero ∉ map fsuc xs
  0∉map-fsuc [] ()
  0∉map-fsuc (x ∷ xs) (there 0∈mapᶠxs) = 0∉map-fsuc xs 0∈mapᶠxs

  ∉-tabulate : ∀ {a n} {A : Set a} (f : Fin n → A) {v : A} → (∀ i → f i ≢ v) → v ∉ tabulate f
  ∉-tabulate {n = zero}  _ _   ()
  ∉-tabulate {n = suc n} _ v∉f here           = v∉f fzero refl
  ∉-tabulate {n = suc n} f v∉f (there v∈tabᶠ) = ∉-tabulate (f ∘ fsuc) (v∉f ∘ fsuc) v∈tabᶠ

  allPairs-∃-∈ : ∀ {a} {A : Set a} {m n : ℕ} {xs : Vec A m} {ys : Vec A n} {v} → v ∈ allPairs xs ys → ∃₂ λ x y → v ≡ (x , y)
  allPairs-∃-∈ {v = (x , y)} xy∈allPairs = x , y , refl
-}
