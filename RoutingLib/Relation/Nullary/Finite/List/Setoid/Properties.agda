
open import Relation.Binary

open import RoutingLib.Relation.Nullary.Finite.List.Setoid

module RoutingLib.Relation.Nullary.Finite.List.Setoid.Properties 
  {a ℓ} {S : Setoid a ℓ} (finite : Finite S)
  where

open import Data.Fin
open import Data.List
open import Data.List.Relation.Unary.Any using (index)
import Data.List.Membership.Setoid as Membership
open import Data.List.Membership.Setoid.Properties
open import Data.List.Properties
open import Data.Product hiding (map)
open import Data.Nat as ℕ
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function
open import Level
open import Relation.Nullary
import Relation.Nullary.Decidable as Dec
open import Relation.Binary.PropositionalEquality using (_≡_; setoid; cong)
open import Data.Product.Relation.Pointwise.NonDependent using (_×ₛ_)
open import Data.Sum.Relation.Pointwise using (_⊎ₛ_; inj₁; inj₂)

open import RoutingLib.Data.List
open import RoutingLib.Data.List.Properties
open import RoutingLib.Data.List.Membership.Setoid.Properties
import RoutingLib.Data.List.Membership.DecSetoid as DecMembership
import RoutingLib.Data.List.Relation.Unary.Unique.Setoid.Properties as Unique
import RoutingLib.Data.List.Relation.Unary.Complete.Setoid.Properties as Complete
import RoutingLib.Function.Properties.Bijection as Bijection
import RoutingLib.Relation.Nullary.Finite.Bijection.Setoid as Bijection

private
  variable
    b ℓ₁ ℓ₂ p : Level

open Setoid S renaming (Carrier to A)
open Finite finite

module _ where

  open Membership S

  Finite⇒Finiteₛ : Bijection.Finite S
  Finite⇒Finiteₛ = record
    { n         = length xs
    ; bijection = record
      { f         = index ∘ complete
      ; cong      = index-cong S (complete _) (complete _) unique
      ; bijective = index-injective S unique , λ i → lookup xs i , index-lookup S unique (complete _)
      }
    }

module _ (T? : DecSetoid b ℓ₂) where

  open DecSetoid T? using () renaming (setoid to T)
  open DecMembership T?
  
  via-dec-surjection : Surjection S T → Finite T
  via-dec-surjection surj = record
    { xs       = deduplicate (map f xs)
    ; complete = Complete.deduplicate⁺ T? (Complete.map⁺ S T complete isSurjection)
    ; unique   = Unique.deduplicate⁺ T? (map f xs)
    } where open Surjection surj
