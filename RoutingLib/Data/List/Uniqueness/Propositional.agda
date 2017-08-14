open import Data.List
open import Data.Fin using (Fin)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (setoid; _≡_; _≢_; refl)
open import Function using (id)

open import RoutingLib.Data.List using (allFin; combine)
open import RoutingLib.Data.List.Disjoint using (_#_)
open import RoutingLib.Data.List.Uniqueness using () renaming (Unique to Unique')
open import RoutingLib.Data.List.Membership.Propositional using (deduplicate)
import RoutingLib.Data.List.Uniqueness.Properties as UP

module RoutingLib.Data.List.Uniqueness.Propositional where

  Unique : ∀ {a} {A : Set a} → List A → Set a
  Unique {A = A} xs = Unique' (setoid A) xs

  allFin!⁺ : ∀ n → Unique (allFin n)
  allFin!⁺ n = UP.tabulate! (setoid (Fin n)) id id
  
  combine!⁺ : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c}
             (f : A → B → C) → 
             (∀ {w x y z} → (w ≢ y) ⊎ (x ≢ z) → f w x ≢ f y z) →
             ∀ {xs ys} → Unique xs → Unique ys → Unique (combine f xs ys)
  combine!⁺ {A = A} {B} {C} f cong xs! ys! = UP.combine!⁺ (setoid A) (setoid B) (setoid C) f cong xs! ys!

  ++!⁺ : ∀ {a} {A : Set a} {xs ys} → Unique xs → Unique ys → _#_ (setoid A) xs ys → Unique (xs ++ ys)
  ++!⁺ = UP.++!⁺ (setoid _)
  
  deduplicate!⁺ : ∀ {a} {A : Set a} _≟_ (xs : List A) → Unique (deduplicate _≟_ xs)
  deduplicate!⁺ = UP.deduplicate!⁺ (setoid _)

  map!⁺ : ∀ {a b} {A : Set a} {B : Set b}
            {f : A → B} → (∀ {x y} → x ≢ y → f x ≢ f y) →
            ∀ {xs} → Unique xs → Unique (map f xs)
  map!⁺ = UP.map!⁺ (setoid _) (setoid _)
