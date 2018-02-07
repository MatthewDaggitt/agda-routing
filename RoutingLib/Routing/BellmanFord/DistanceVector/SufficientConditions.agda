open import Level using (_⊔_)
open import Data.Product using (∃; _×_; proj₁; proj₂)
open import Data.Sum using (_⊎_)
open import Data.List using (List)
import Data.List.Any.Membership as Membership
open import Relation.Binary
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)
open import Algebra.Structures using (IsSemigroup)
import Algebra.FunctionProperties as FunctionProperties
open import Function using (flip)
import Relation.Binary.NonStrictToStrict as NonStrictToStrict
import Relation.Binary.Flip as Flip
open import Function using (_∘_)

import RoutingLib.Algebra.Selectivity.RightNaturalOrder as RightNaturalOrder
open import RoutingLib.Routing.Definitions
open import RoutingLib.Relation.Binary.RespectedBy using (_RespectedBy_)
open import RoutingLib.Data.List.Uniset using (Enumeration)
open import RoutingLib.Algebra.Selectivity.Properties using (idem)

module RoutingLib.Routing.BellmanFord.DistanceVector.SufficientConditions  where

  -------------------
  -- Without paths --
  -------------------
  -- Sufficient conditions for the convergence of the synchronous
  -- Distributed Bellman Ford from any state

  record SufficientConditions
    {a b ℓ} (𝓡𝓐 : RoutingAlgebra a b ℓ) : Set (a ⊔ b ⊔ ℓ) where

    open RoutingAlgebra 𝓡𝓐
    open FunctionProperties _≈_
    open Membership S using (_∈_)

    field
      -- Operator properties
      ⊕-assoc : Associative _⊕_
      ⊕-sel   : Selective   _⊕_
      ⊕-comm  : Commutative _⊕_
      ⊕-almost-strictly-absorbs-▷ : ∀ f {x} → x ≉ 0# → x <₊ (f ▷ x)

      -- Special element properties
      ▷-zero     : ∀ f → f ▷ 0# ≈ 0#
      ⊕-zeroʳ     : RightZero 1# _⊕_
      ⊕-identityʳ : RightIdentity 0# _⊕_

      -- Finiteness of routes
      allRoutes   : List Route
      ∈-allRoutes : ∀ r → r ∈ allRoutes


    -- Immediate properties about the algebra

    ⊕-idem : Idempotent _⊕_
    ⊕-idem = idem _≈_ _⊕_ ⊕-sel

    ⊕-isSemigroup : IsSemigroup _≈_ _⊕_
    ⊕-isSemigroup = record
      { isEquivalence = ≈-isEquivalence
      ; assoc         = ⊕-assoc
      ; ∙-cong        = ⊕-cong
      }
      
    open RightNaturalOrder _≈_ _⊕_ using ()
      renaming (≤-decTotalOrder to ass⇨≤-decTotalOrder)
    
    ≤₊-decTotalOrder : DecTotalOrder b ℓ ℓ
    ≤₊-decTotalOrder = ass⇨≤-decTotalOrder ⊕-isSemigroup _≟_ ⊕-comm ⊕-sel

    open DecTotalOrder ≤₊-decTotalOrder public
      using ()
      renaming
      ( _≤?_      to _≤₊?_
      ; refl      to ≤₊-refl
      ; reflexive to ≤₊-reflexive
      ; trans     to ≤₊-trans
      ; antisym   to ≤₊-antisym
      ; poset     to ≤₊-poset
      ; total     to ≤₊-total
      ; ≤-resp-≈  to ≤₊-resp-≈
      )

    ≥₊-isDecTotalOrder : IsDecTotalOrder _≈_ (flip _≤₊_)
    ≥₊-isDecTotalOrder = record
      { isTotalOrder = record
          { isPartialOrder = record
            { isPreorder = record
              { isEquivalence = ≈-isEquivalence
              ; reflexive     = ≤₊-reflexive ∘ ≈-sym
              ; trans         = Flip.transitive _≤₊_ ≤₊-trans
              }
            ; antisym    = λ y≤x x≤y → ≤₊-antisym x≤y y≤x
            }
          ; total        = Flip.total _ ≤₊-total
          }
      ; _≟_          = _≟_
      ; _≤?_         = Flip.decidable _≤₊_ _≤₊?_
      }
    
    ≥₊-decTotalOrder : DecTotalOrder _ _ _
    ≥₊-decTotalOrder = record
      { Carrier         = Route
      ; _≈_             = _≈_
      ; _≤_             = flip _≤₊_
      ; isDecTotalOrder = ≥₊-isDecTotalOrder
      }

    open NonStrictToStrict _≈_ _≤₊_ using () renaming (<-resp-≈ to <-resp-≈')

    <₊-resp-≈ᵣ : _
    <₊-resp-≈ᵣ = proj₁ (<-resp-≈' ≈-isEquivalence ≤₊-resp-≈)

    <₊-resp-≈ₗ : _
    <₊-resp-≈ₗ = proj₂ (<-resp-≈' ≈-isEquivalence ≤₊-resp-≈)
    
    ⊕-identityˡ : LeftIdentity 0# _⊕_
    ⊕-identityˡ x = ≈-trans (⊕-comm 0# x) (⊕-identityʳ x)
