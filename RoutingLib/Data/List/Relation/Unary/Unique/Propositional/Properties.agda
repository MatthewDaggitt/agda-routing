
module RoutingLib.Data.List.Relation.Unary.Unique.Propositional.Properties where

open import Data.List
open import Data.List.Relation.Unary.Unique.Propositional
import Data.List.Relation.Unary.AllPairs as AllPairs
open import Data.Product using (_×_)
open import Data.Product.Relation.Binary.Pointwise.NonDependent
open import Level
open import Relation.Binary.PropositionalEquality using (setoid; decSetoid; _≡_)
open import Function using (_∘_; id)

open import RoutingLib.Data.List
open import RoutingLib.Data.List.Membership.DecPropositional using (deduplicate)
import RoutingLib.Data.List.Relation.Unary.Unique.Setoid.Properties as SP

private
  variable
    a b c : Level
    A : Set a
    B : Set b
    C : Set c
    
combine⁺ : (f : A → B → C) →
           (∀ {w x y z} → f w x ≡ f y z → (w ≡ y) × (x ≡ z)) →
           ∀ {xs ys} → Unique xs → Unique ys → Unique (combine f xs ys)
combine⁺ f cong = SP.combine⁺ (setoid _) (setoid _) (setoid _) f cong

allPairs⁺ : ∀ {xs ys} → Unique xs → Unique ys → Unique (allPairs xs ys)
allPairs⁺ xs! ys! = {!SP.allPairs⁺ ? ? ? ?!}

deduplicate⁺ : ∀ {a} {A : Set a} _≟_ (xs : List A) → Unique (deduplicate _≟_ xs)
deduplicate⁺ _≟_ = SP.deduplicate⁺ (decSetoid _≟_)
