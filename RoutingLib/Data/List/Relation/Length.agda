open import Data.List
open import Data.Nat using (_≤_)
open import Level using () renaming (zero to ℓ₀)
open import Function using (_on_)
open import Relation.Binary using (Rel)
open import Relation.Binary.On as On

open import RoutingLib.Data.Nat.Properties using (≤-decTotalPreorder)
open import RoutingLib.Relation.Binary.On using (decTotalPreorder)
open import RoutingLib.Relation.Binary using (DecTotalPreorder)

module RoutingLib.Data.List.Relation.Length where

  ≤ₗ-decTotalPreorder : ∀ {a} (A : Set a) → DecTotalPreorder a ℓ₀ ℓ₀
  ≤ₗ-decTotalPreorder A = decTotalPreorder ≤-decTotalPreorder (length {A = A})

  module _ {a} {A : Set a} where

    open DecTotalPreorder (≤ₗ-decTotalPreorder A) public
      using () renaming
      ( _≤_ to _≤ₗ_
      ; reflexive       to ≤ₗ-reflexive
      ; refl            to ≤ₗ-refl
      ; trans           to ≤ₗ-trans
      ; total           to ≤ₗ-total
      ; isPreorder      to ≤ₗ-isPreorder
      ; isTotalPreorder to ≤ₗ-isTotalPreorder
      )

  test : 1 ∷ 2 ∷ [] ≤ₗ 3 ∷ 4 ∷ 5 ∷ []
  test = {!!}

  
