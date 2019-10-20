
module RoutingLib.Relation.Nullary.Finite.List.Setoid where

open import Data.List
open import Data.List.Relation.Unary.Any using (index)
import Data.List.Membership.Setoid as Membership
open import Data.List.Membership.Setoid.Properties
open import Data.Product hiding (map)
open import Data.Nat
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function
open import Level
open import Relation.Nullary
open import Relation.Unary using (Pred; Decidable)
import Relation.Nullary.Decidable as Dec
open import Relation.Binary hiding (Decidable)
open import Relation.Binary.PropositionalEquality using (setoid)
open import Data.Product.Relation.Pointwise.NonDependent using (_×ₛ_)
open import Data.Sum.Relation.Pointwise using (_⊎ₛ_; inj₁; inj₂)

open import RoutingLib.Relation.Nullary hiding (Finite)
open import RoutingLib.Data.List
open import RoutingLib.Data.List.Membership.Setoid.Properties
open import RoutingLib.Function

private
  variable
    a b ℓ ℓ₁ ℓ₂ p : Level
    
Finite : Setoid a ℓ → Set _
Finite S = ∃ λ xs → ∀ x → x ∈ xs
  where open Membership S

module _ {S : Setoid a ℓ₁} where

  open Membership S
  
  Finite⇒Finiteₛ : Finite S → Finiteₛ S
  Finite⇒Finiteₛ (xs , _∈xs) = record
    { n         = length xs
    ; bijection = record
      { f         = λ x → index (x ∈xs)
      ; cong      = {!!}
      ; bijective = {!!}
      }
    }

module _ {S : Setoid a ℓ₁} {T : Setoid b ℓ₂} where

  _×ᶠ_ : Finite S → Finite T → Finite (S ×ₛ T)
  (xs , _∈xs) ×ᶠ (ys , _∈ys) = xs×ys , _∈xs×ys
    where
    xs×ys : List _
    xs×ys = allPairs xs ys

    _∈xs×ys : ∀ x×y → _
    (x , y) ∈xs×ys = ∈-allPairs⁺ S T (x ∈xs) (y ∈ys)

  _⊎ᶠ_ : Finite S → Finite T → Finite (S ⊎ₛ T)
  (xs , _∈xs) ⊎ᶠ (ys , _∈ys) = xs⊎ys , _∈xs⊎ys
    where
    xs⊎ys : List _
    xs⊎ys = map inj₁ xs ++ map inj₂ ys
    
    _∈xs⊎ys : ∀ x⊎y → _
    (inj₁ x) ∈xs⊎ys = ∈-++⁺ˡ (S ⊎ₛ T) (∈-map⁺ S (S ⊎ₛ T) inj₁ (x ∈xs))
    (inj₂ y) ∈xs⊎ys = ∈-++⁺ʳ (S ⊎ₛ T) _ (∈-map⁺ T (S ⊎ₛ T) inj₂ (y ∈ys))
