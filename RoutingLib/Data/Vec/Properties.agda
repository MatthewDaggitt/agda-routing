open import Data.Nat as ℕ using (ℕ; zero; suc; z≤n; s≤s; _+_)
open import Data.Nat.Properties using (≤-trans; n≤1+n)
open import Data.Fin using (Fin; _<_; _≤_; inject₁) renaming (zero to fzero; suc to fsuc)
open import Algebra.FunctionProperties using (Op₂)
open import Data.Vec
open import Data.Product using (∃; ∃₂; _,_; _×_) renaming (map to mapₚ)
open import Data.List using ([]; _∷_)
open import Data.List.Any as Any using (here; there)
open import Data.List.Membership.Propositional using () renaming (_∈_ to _∈ₗ_)
open import Function using (_∘_; id)
open import Relation.Unary using (Pred; Decidable)
open import Relation.Nullary using (yes; no; ¬_)
open import Relation.Binary using () renaming (Decidable to BDecidable)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym)

open import RoutingLib.Data.Vec

module RoutingLib.Data.Vec.Properties where

  ≟-Vec : ∀ {a n} {A : Set a} → BDecidable {A = A} _≡_ → BDecidable {A = Vec A n} _≡_
  ≟-Vec _≟_ []       []       = yes refl
  ≟-Vec _≟_ (x ∷ xs) (y ∷ ys) with x ≟ y | ≟-Vec _≟_ xs ys
  ... | yes refl | yes refl = yes refl
  ... | no  x≢y  | _        = no λ { refl → x≢y refl }
  ... | _        | no xs≢ys = no λ { refl → xs≢ys refl }

  ∈-lookup : ∀ {a n} {A : Set a} {v : A} {xs : Vec A n} →
             v ∈ xs → ∃ λ i → lookup i xs ≡ v
  ∈-lookup here = fzero , refl
  ∈-lookup (there v∈xs) = mapₚ fsuc id (∈-lookup v∈xs)

  ∈-lookup⁺ : ∀ {a n} {A : Set a} i (xs : Vec A n) → lookup i xs ∈ xs
  ∈-lookup⁺ fzero    (x ∷ xs) = here
  ∈-lookup⁺ (fsuc i) (x ∷ xs) = there (∈-lookup⁺ i xs)

  ∈-fromList⁻ : ∀ {a} {A : Set a} {v : A} {xs} → v ∈ fromList xs → v ∈ₗ xs
  ∈-fromList⁻ {xs = []}    ()
  ∈-fromList⁻ {xs = _ ∷ _} here         = here refl
  ∈-fromList⁻ {xs = _ ∷ _} (there v∈xs) = there (∈-fromList⁻ v∈xs)

  lookup-zipWith : ∀ {a b c n} {A : Set a} {B : Set b} {C : Set c} (f : A → B → C)
                   (i : Fin n) xs ys →
                   lookup i (zipWith f xs ys) ≡ f (lookup i xs) (lookup i ys)
  lookup-zipWith _ fzero    (x ∷ _)  (y ∷ _)   = refl
  lookup-zipWith _ (fsuc i) (_ ∷ xs) (_ ∷ ys)  = lookup-zipWith _ i xs ys


  -- stdlib
  count≤n : ∀ {a p} {A : Set a} {P : Pred A p} → (P? : Decidable P) →
            ∀ {n} → (xs : Vec A n) → count P? xs ℕ.≤ n
  count≤n P? []       = z≤n
  count≤n P? (x ∷ xs) with P? x
  ... | yes _ = s≤s (count≤n P? xs)
  ... | no  _ = ≤-trans (count≤n P? xs) (n≤1+n _)


  ∉-extend : ∀ {a n} {A : Set a} {v x : A} {xs : Vec A n} → ¬ (v ≡ x) → v ∉ xs → v ∉ (x ∷ xs)
  ∉-extend v≢x v∉xs here         = v≢x refl
  ∉-extend _   v∉xs (there v∈xs) = v∉xs v∈xs
