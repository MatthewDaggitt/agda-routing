
open import Relation.Binary

open import RoutingLib.Relation.Nullary.Finite.List.Setoid

module RoutingLib.Relation.Nullary.Finite.List.Setoid.Properties 
  
  where

open import Data.Fin hiding (_≟_)
open import Data.List
open import Data.List.Relation.Unary.Any using (index)
import Data.List.Relation.Unary.Unique.Setoid.Properties as Unique
import Data.List.Membership.Setoid as Membership
open import Data.List.Membership.Setoid.Properties
open import Data.List.Properties
open import Data.Product hiding (map)
open import Data.Nat as ℕ hiding (_≟_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function
open import Level
open import Relation.Nullary
import Relation.Nullary.Decidable as Dec
open import Relation.Binary.PropositionalEquality using (_≡_; setoid; cong)
open import Data.Product.Relation.Binary.Pointwise.NonDependent using (_×ₛ_)
open import Data.Sum.Relation.Binary.Pointwise using (_⊎ₛ_; inj₁; inj₂)

open import RoutingLib.Data.List
open import RoutingLib.Data.List.Properties
open import RoutingLib.Data.List.Membership.Setoid.Properties
import RoutingLib.Data.List.Relation.Unary.Unique.Setoid.Properties as Unique
import RoutingLib.Data.List.Relation.Unary.Complete.Setoid.Properties as Complete
import RoutingLib.Function.Properties.Bijection as Bijection
import RoutingLib.Relation.Nullary.Finite.Bijection.Setoid as Bijection

private
  variable
    a b ℓ₁ ℓ₂ p : Level
    S : Setoid a ℓ₁

module _ where

  Finite⇒Finiteₛ : Finite S → Bijection.Finite S
  Finite⇒Finiteₛ {S = S} finite = record
    { n         = length xs
    ; bijection = record
      { f         = index ∘ complete
      ; cong      = index-cong S (complete _) (complete _) unique
      ; bijective = index-injective S unique , λ i → lookup xs i , index-lookup S unique (complete _)
      }
    } where open Finite finite
{-
  Finiteₛ⇒Finite : Bijection.Finite S → Finite S
  Finiteₛ⇒Finite {S = S} finite = record
    { xs       = tabulate f⁻¹
    ; complete = λ x → ∈-resp-≈ S (f⁻¹∘f x) (∈-tabulate⁺ S (f x))
    ; unique   = Unique.tabulate⁺ S λ v≈u → {!!}
    } where open Bijection.Finite finite
-}
module _ (finite : Finite S) (T? : DecSetoid b ℓ₂) where

  open DecSetoid T? using (_≟_) renaming (setoid to T)
  open Finite finite
  
  via-dec-surjection : Surjection S T → Finite T
  via-dec-surjection surj = record
    { xs       = deduplicate _≟_ (map f xs)
    ; complete = Complete.deduplicate⁺ T? (Complete.map⁺ S T complete isSurjection)
    ; unique   = Unique.deduplicate⁺ T? (map f xs)
    } where open Surjection surj
