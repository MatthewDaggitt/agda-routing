open import Data.List
open import Data.Fin using (Fin)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Nat.Properties using (<⇒≢)
open import Relation.Binary.PropositionalEquality using (setoid; _≡_; _≢_; refl; decSetoid)
open import Function using (id)

open import RoutingLib.Data.List using (combine; between)
open import RoutingLib.Data.List.Disjoint using (_#_)
open import RoutingLib.Data.List.Membership.DecPropositional using (deduplicate)
open import RoutingLib.Data.List.All.Properties using (AllPairs-applyUpTo⁺₁; AllPairs-applyBetween⁺₁)
open import RoutingLib.Data.List.Uniqueness.Propositional
import RoutingLib.Data.List.Uniqueness.Setoid.Properties as SP

module RoutingLib.Data.List.Uniqueness.Propositional.Properties where

  allFin!⁺ : ∀ n → Unique (allFin n)
  allFin!⁺ n = SP.tabulate! (setoid (Fin n)) id id
  
  combine!⁺ : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c}
             (f : A → B → C) → 
             (∀ {w x y z} → (w ≢ y) ⊎ (x ≢ z) → f w x ≢ f y z) →
             ∀ {xs ys} → Unique xs → Unique ys → Unique (combine f xs ys)
  combine!⁺ f cong = SP.combine!⁺ (setoid _) (setoid _) (setoid _) f cong

  ++!⁺ : ∀ {a} {A : Set a} {xs ys} → Unique xs → Unique ys → _#_ (setoid A) xs ys → Unique (xs ++ ys)
  ++!⁺ = SP.++!⁺ (setoid _)
  
  deduplicate!⁺ : ∀ {a} {A : Set a} _≟_ (xs : List A) → Unique (deduplicate _≟_ xs)
  deduplicate!⁺ _≟_ = SP.deduplicate!⁺ (decSetoid _≟_)

  map!⁺ : ∀ {a b} {A : Set a} {B : Set b}
            {f : A → B} → (∀ {x y} → x ≢ y → f x ≢ f y) →
            ∀ {xs} → Unique xs → Unique (map f xs)
  map!⁺ = SP.map!⁺ (setoid _) (setoid _)

  upTo!⁺ : ∀ n → Unique (upTo n)
  upTo!⁺ n = AllPairs-applyUpTo⁺₁ id n (λ i<j _ → <⇒≢ i<j)

  between!⁺ : ∀ s e → Unique (between s e)
  between!⁺ s e = AllPairs-applyBetween⁺₁ id s e (λ _ i<j _ → <⇒≢ i<j)
