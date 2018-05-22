open import Data.Nat using (ℕ; _<_)
open import Data.Fin using (Fin)
open import Level using () renaming (zero to ℓ₀)
open import Relation.Binary using (Rel)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Nullary using (¬_)

open import RoutingLib.Data.SimplePath.NonEmpty using (SimplePathⁿᵗ; length)
open import RoutingLib.Data.SimplePath.NonEmpty.Relation.Equality using (_≈ₚ_)
open import RoutingLib.Data.SimplePath.NonEmpty.Relation.Lex using (_<ₗₑₓ_)
open import RoutingLib.Routing.BellmanFord.Models.BGPLite.Communities

module RoutingLib.Routing.BellmanFord.Models.BGPLite.Route (n : ℕ) where

-----------
-- Types --
-----------

Level : Set
Level = ℕ

Node : Set
Node = Fin n

data Route : Set where
  invalid : Route
  route   : (l : ℕ) → (cs : CommunitySet) → (p : SimplePathⁿᵗ n) → Route

--------------
-- Equality --
--------------

infix 4 _≈ᵣ_ _≉ᵣ_

data _≈ᵣ_ : Rel Route ℓ₀ where
  invalidEq : invalid ≈ᵣ invalid
  routeEq   : ∀ {k l cs ds p q} → k ≡ l → cs ≈ᶜˢ ds → p ≈ₚ q → route k cs p ≈ᵣ route l ds q 

_≉ᵣ_ : Rel Route ℓ₀
r ≉ᵣ s = ¬ (r ≈ᵣ s)

----------------------
-- Preference order --
----------------------

infix 4 _≤ᵣ_

data _≤ᵣ_ : Rel Route ℓ₀ where
  invalid : ∀ {r} → r ≤ᵣ invalid
  level<  : ∀ {k l cs ds p q} → k < l → route k cs p ≤ᵣ route l ds q
  length< : ∀ {k l cs ds p q} → k ≡ l → length p < length q → route k cs p ≤ᵣ route l ds q
  plex<   : ∀ {k l cs ds p q} → k ≡ l → length p ≡ length q → p <ₗₑₓ q → route k cs p ≤ᵣ route l ds q
  comm≤   : ∀ {k l cs ds p q} → k ≡ l → p ≈ₚ q → cs ≤ᶜˢ ds → route k cs p ≤ᵣ route l ds q
