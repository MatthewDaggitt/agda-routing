
module RoutingLib.Relation.Nullary.Finite.List.Setoid where

open import Data.List
open import Data.List.Relation.Unary.Any using (index)
import Data.List.Membership.Setoid as Membership
open import Data.List.Membership.Setoid.Properties
open import Data.List.Relation.Unary.Unique.Setoid
open import Data.List.Relation.Binary.Disjoint.Setoid
import Data.Fin.Properties as Fin
import Data.List.Relation.Unary.Unique.Setoid.Properties as Unique
import Data.List.Relation.Unary.Unique.Propositional.Properties as Uniqueₚ
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Product.Relation.Binary.Pointwise.NonDependent
open import Data.Sum as Sum using (inj₁; inj₂)
open import Data.Sum.Relation.Binary.Pointwise hiding (map)
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
    { xs       = cartesianProduct SF.xs TF.xs
    ; complete = Complete.cartesianProduct⁺ S T SF.complete TF.complete
    ; unique   = Unique.cartesianProduct⁺   S T SF.unique   TF.unique
    } where module SF = Finite fin₁; module TF = Finite fin₂

  _⊎ᶠ_ : Finite S → Finite T → Finite (S ⊎ₛ T)
  fin₁ ⊎ᶠ fin₂ = record
    { xs       = map inj₁ SF.xs ++ map inj₂ TF.xs
    ; complete = Complete.++⁺ S T SF.complete TF.complete
    ; unique   = Unique.++⁺ (S ⊎ₛ T)
                   (Unique.map⁺ S (S ⊎ₛ T) drop-inj₁ SF.unique)
                   (Unique.map⁺ T (S ⊎ₛ T) drop-inj₂ TF.unique)
                   disjoint
    }
    where
    module SF = Finite fin₁
    module TF = Finite fin₂

    disjoint : Disjoint (S ⊎ₛ T) (map inj₁ SF.xs) (map inj₂ TF.xs)
    disjoint {inj₁ x} (_ , x∈ys) with ∈-map⁻ T (S ⊎ₛ T) x∈ys
    ... | _ , _ , ()
    disjoint {inj₂ y} (y∈xs , _) with ∈-map⁻ S (S ⊎ₛ T) y∈xs
    ... | _ , _ , ()

------------------------------------------------------------------------
-- Examples

Fin-finite : ∀ n → Finite (Fin.≡-setoid n)
Fin-finite n = record
  { xs       = allFin n
  ; complete = Complete.allFin⁺ n
  ; unique   = Uniqueₚ.allFin⁺ n
  }
