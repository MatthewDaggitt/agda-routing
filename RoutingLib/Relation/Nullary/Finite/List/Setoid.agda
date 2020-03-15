
module RoutingLib.Relation.Nullary.Finite.List.Setoid where

open import Data.List
open import Data.List.Relation.Unary.Any using (index)
import Data.List.Membership.Setoid as Membership
open import Data.List.Membership.Setoid.Properties
open import Data.List.Relation.Unary.Unique.Setoid
import Data.List.Relation.Unary.Unique.Setoid.Properties as Unique
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Product.Relation.Binary.Pointwise.NonDependent
open import Data.Sum as Sum using (inj₁; inj₂)
open import Data.Sum.Relation.Binary.Pointwise
open import Level
open import Relation.Nullary
import Relation.Nullary.Decidable as Dec
open import Relation.Binary

open import RoutingLib.Data.List
open import RoutingLib.Data.List.Membership.Setoid.Properties
open import RoutingLib.Data.List.Relation.Unary.Complete.Setoid
import RoutingLib.Data.List.Relation.Unary.Unique.Setoid.Properties as Unique
import RoutingLib.Data.List.Relation.Unary.Complete.Setoid.Properties as Complete
import RoutingLib.Relation.Nullary.Finite.Bijection.Setoid as Bijection

private
  variable
    a b ℓ ℓ₁ ℓ₂ p : Level

------------------------------------------------------------------------
-- Definition

record Finite (S : Setoid a ℓ) : Set (a ⊔ suc ℓ) where
  open Setoid using (Carrier)
  open Membership S
  
  field
    xs       : List (Carrier S)
    complete : ∀ x → x ∈ xs
    unique   : Unique S xs

------------------------------------------------------------------------
-- Other constructors

module _ (S? : DecSetoid a ℓ) where
  open DecSetoid S? renaming (setoid to S)
  
  complete? : ∀ {xs} → Complete S xs → Finite S
  complete? {xs} complete = record
    { xs       = deduplicate _≟_ xs
    ; complete = Complete.deduplicate⁺ S? complete
    ; unique   = Unique.deduplicate⁺   S? xs
    }

------------------------------------------------------------------------
-- Combinators

module _ {S : Setoid a ℓ₁} {T : Setoid b ℓ₂} where

  _×ᶠ_ : Finite S → Finite T → Finite (S ×ₛ T)
  fin₁ ×ᶠ fin₂ = record
    { xs       = allPairs SF.xs TF.xs
    ; complete = Complete.allPairs⁺ S T SF.complete TF.complete
    ; unique   = Unique.allPairs⁺   S T SF.unique   TF.unique
    } where module SF = Finite fin₁; module TF = Finite fin₂
{-
  _⊎ᶠ_ : Finite S → Finite T → Finite (S ⊎ₛ T)
  fin₁ ⊎ᶠ fin₂ = record
    { xs       = map inj₁ SF.xs ++ map inj₂ TF.xs
    ; complete = λ x → ∈-++⁺ (S ⊎ₛ T) (map inj₁ SF.xs) (map inj₂ TF.xs) (Sum.map {!∈-map⁺ ? ? ?!} {!!} x) 
    ; unique   = Unique.++⁺ (S ⊎ₛ T) {!!} {!!} {!!}
    } where module SF = Finite fin₁; module TF = Finite fin₂
-}
