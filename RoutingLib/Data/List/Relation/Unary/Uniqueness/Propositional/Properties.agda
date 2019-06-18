
module RoutingLib.Data.List.Relation.Unary.Uniqueness.Propositional.Properties where

open import Data.List
open import Data.List.Relation.Unary.Unique.Propositional
open import Data.Product using (_×_)
open import Relation.Binary.PropositionalEquality using (setoid; decSetoid; _≡_)
open import Function using (_∘_; id)

open import RoutingLib.Data.List using (combine)
open import RoutingLib.Data.List.Membership.DecPropositional using (deduplicate)
import RoutingLib.Data.List.Relation.Unary.Uniqueness.Setoid.Properties as SP

combine!⁺ : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c}
           (f : A → B → C) →
           (∀ {w x y z} → f w x ≡ f y z → (w ≡ y) × (x ≡ z)) →
           ∀ {xs ys} → Unique xs → Unique ys → Unique (combine f xs ys)
combine!⁺ f cong = SP.combine!⁺ (setoid _) (setoid _) (setoid _) f cong

deduplicate!⁺ : ∀ {a} {A : Set a} _≟_ (xs : List A) → Unique (deduplicate _≟_ xs)
deduplicate!⁺ _≟_ = SP.deduplicate!⁺ (decSetoid _≟_)
