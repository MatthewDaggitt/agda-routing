open import Level using (_⊔_)
open import Data.Product using (∃; _×_; proj₁; proj₂)
open import Data.Sum using (_⊎_)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)
import Algebra.FunctionProperties as FunctionProperties

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
    
    field
      -- Operator properties
      ⊕-assoc : Associative _⊕_
      ⊕-sel   : Selective   _⊕_
      ⊕-comm  : Commutative _⊕_
      ⊕-almost-strictly-absorbs-▷ : ∀ s {r} → r ≉ 0# → ((s ▷ r) ⊕ r ≈ r) × (r ≉ s ▷ r)

      -- Special element properties
      0#-idᵣ-⊕ : RightIdentity 0# _⊕_
      0#-an-▷ : ∀ s → s ▷ 0# ≈ 0#
      1#-anᵣ-⊕ : RightZero 1# _⊕_

      -- Other properties
      routes-enumerable : Enumeration DS



    -- Immediate properties about the algebra

    ⊕-idem : Idempotent _⊕_
    ⊕-idem = idem _≈_ _⊕_ ⊕-sel

    open import RoutingLib.Algebra.Selectivity.NaturalOrders S _⊕_ ⊕-cong using () renaming (_≤ᵣ_ to _≤_; _≰ᵣ_ to _≰_; ≤ᵣ-respᵣ-≈ to ≤-respᵣ-≈; ≤ᵣ-respₗ-≈ to ≤-respₗ-≈) public
    open import RoutingLib.Algebra.Selectivity.NaturalOrders S _⊕_ ⊕-cong using () renaming (≤ᵣ-total to ass⇨≤-total; ≤ᵣ-poset to ass⇨≤-poset; ≤ᵣ-decTotalOrder to ass⇨≤-decTotalOrder)
    open import Relation.Binary.NonStrictToStrict _≈_ _≤_ using (_<_) public
    open import Relation.Binary.NonStrictToStrict _≈_ _≤_ using () renaming (<-resp-≈ to <-resp-≈')
    
    _≤?_ : Decidable _≤_
    x ≤? y = y ⊕ x ≟ x

    ≤-total : Total _≤_
    ≤-total = ass⇨≤-total ⊕-sel ⊕-comm

    --≤-poset : Poset b ℓ ℓ
    --≤-poset = ass⇨≤-poset ⊕-comm ⊕-assoc ⊕-idem

    ≤-decTotalOrder : DecTotalOrder b ℓ ℓ
    ≤-decTotalOrder = ass⇨≤-decTotalOrder _≟_ ⊕-comm ⊕-assoc ⊕-sel
    
    open DecTotalOrder ≤-decTotalOrder public
      using (≤-resp-≈)
      renaming
      ( refl      to ≤-refl
      ; reflexive to ≤-reflexive
      ; trans     to ≤-trans
      ; antisym   to ≤-antisym
      )

    <-resp-≈ᵣ : _
    <-resp-≈ᵣ = proj₁ (<-resp-≈' isEquivalence ≤-resp-≈)

    <-resp-≈ₗ : _
    <-resp-≈ₗ = proj₂ (<-resp-≈' isEquivalence ≤-resp-≈)
    
    0#-idₗ-⊕ : LeftIdentity 0# _⊕_
    0#-idₗ-⊕ x = ≈-trans (⊕-comm 0# x) (0#-idᵣ-⊕ x)
