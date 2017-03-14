open import Level using (_⊔_)
open import Data.Product using (∃; _×_)
open import Data.Sum using (_⊎_)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)
open import Algebra.FunctionProperties using (Associative; Commutative; LeftIdentity; RightIdentity; RightZero; Idempotent; Selective)

open import RoutingLib.Routing.Definitions
open import RoutingLib.Relation.Binary.RespectedBy using (_RespectedBy_)
open import RoutingLib.Data.List.Enumeration using (Enumeration)
open import RoutingLib.Algebra.Selectivity.Properties using (idem)

module RoutingLib.Routing.Algorithms.BellmanFord.Convergence.SufficientConditions  where

  ----------------
  -- With paths --
  ----------------
  -- Sufficient conditions for the convergence of the synchronous
  -- Distributed Bellman Ford from any state when the algebra
  -- is lexed with paths

  record ConvergenceConditionsWithPaths
    {a b ℓ} (ra : RoutingAlgebra a b ℓ) : Set (a ⊔ b ⊔ ℓ) where

    open RoutingAlgebra ra

    field
      -- Operator properties
      ⊕-assoc : Associative _≈_ _⊕_
      ⊕-sel : Selective _≈_ _⊕_
      ⊕-comm : Commutative _≈_ _⊕_
      ⊕-absorbs-▷ : ∀ s r → (s ▷ r) ⊕ r ≈ r

      -- Element properties
      1#-anᵣ-⊕ : RightZero _≈_ 1# _⊕_




  -------------------
  -- Without paths --
  -------------------
  -- Sufficient conditions for the convergence of the synchronous
  -- Distributed Bellman Ford from any state when the algebra
  -- is not lexed with paths

  record ConvergenceConditions
    {a b ℓ} (ra : RoutingAlgebra a b ℓ) : Set (a ⊔ b ⊔ ℓ) where

    open RoutingAlgebra ra

    field
      -- Operator properties
      ⊕-assoc : Associative _≈_ _⊕_
      ⊕-sel   : Selective _≈_ _⊕_
      ⊕-comm  : Commutative _≈_ _⊕_
      ⊕-almost-strictly-absorbs-▷ : ∀ s {r} → r ≉ 0# → ((s ▷ r) ⊕ r ≈ r) × (r ≉ s ▷ r)

      -- Special element properties
      0#-idᵣ-⊕ : RightIdentity _≈_ 0# _⊕_
      0#-anᵣ-▷ : ∀ s → s ▷ 0# ≈ 0#
      1#-anᵣ-⊕ : RightZero _≈_ 1# _⊕_

      -- Other properties
      routes-enumerable : Enumeration S



    -- Immediate properties about the algebra

    ⊕-idem : Idempotent _≈_ _⊕_
    ⊕-idem = idem _≈_ _⊕_ ⊕-sel

    open import RoutingLib.Algebra.Selectivity.NaturalOrders S _⊕_ ⊕-pres-≈ using () renaming (_≤ᵣ_ to _≤_; ≤ᵣ-respᵣ-≈ to ≤-respᵣ-≈; ≤ᵣ-respₗ-≈ to ≤-respₗ-≈) public
    open import RoutingLib.Algebra.Selectivity.NaturalOrders S _⊕_ ⊕-pres-≈ using () renaming (≤ᵣ-total to ass⇨≤-total; ≤ᵣ-poset to ass⇨≤-poset)
    open import Relation.Binary.NonStrictToStrict _≈_ _≤_ using (_<_) public

    _≤?_ : Decidable _≤_
    x ≤? y = y ⊕ x ≟ x

    ≤-total : Total _≤_
    ≤-total = ass⇨≤-total ⊕-sel ⊕-comm

    ≤-poset : Poset b ℓ ℓ
    ≤-poset = ass⇨≤-poset ⊕-comm ⊕-assoc ⊕-idem

    open Poset ≤-poset using () renaming (refl to ≤-refl; trans to ≤-trans; antisym to ≤-antisym) public

    0#-idₗ-⊕ : LeftIdentity _≈_ 0# _⊕_
    0#-idₗ-⊕ x = trans (⊕-comm 0# x) (0#-idᵣ-⊕ x)



{-
    -- Condensed properties for algorithm

    open import RoutingLib.Routing.Algorithms.DistributedBellmanFord rp using (σ; I)
    open import RoutingLib.Routing.Algorithms.DistributedBellmanFord.Properties rp

    σXᵢⱼ≤Aᵢₖ▷Xₖⱼ' : ∀ X i j k → σ X i j ≤ A i k ▷ X k j
    σXᵢⱼ≤Aᵢₖ▷Xₖⱼ' = σXᵢⱼ≤Aᵢₖ▷Xₖⱼ ⊕-sel ⊕-comm ⊕-assoc

    σXᵢⱼ≈Aᵢₖ▷Xₖⱼ⊎Iᵢⱼ' : ∀ X i j → (∃ λ k → σ X i j ≈ A i k ▷ X k j) ⊎ (σ X i j ≈ I i j)
    σXᵢⱼ≈Aᵢₖ▷Xₖⱼ⊎Iᵢⱼ' = σXᵢⱼ≈Aᵢₖ▷Xₖⱼ⊎Iᵢⱼ ⊕-sel

    σXᵢᵢ≈Iᵢᵢ' : ∀ X i → σ X i i ≈ I i i
    σXᵢᵢ≈Iᵢᵢ' = σXᵢᵢ≈Iᵢᵢ ⊕-sel ⊕-assoc ⊕-comm 1#-anᵣ-⊕

    σXᵢᵢ≈σYᵢᵢ' : ∀ X Y i → σ X i i ≈ σ Y i i
    σXᵢᵢ≈σYᵢᵢ' = σXᵢᵢ≈σYᵢᵢ ⊕-sel ⊕-assoc ⊕-comm 1#-anᵣ-⊕

    σXᵢⱼ≈σYᵢⱼ' : ∀ X Y i j → (∀ k → (A i k ▷ X k j ≈ A i k ▷ Y k j) ⊎ ((∃ λ l → (A i l ▷ X l j) < (A i k ▷ X k j)) × (∃ λ m → (A i m ▷ Y m j) < (A i k ▷ Y k j)))) → σ X i j ≈ σ Y i j
    σXᵢⱼ≈σYᵢⱼ' = σXᵢⱼ≈σYᵢⱼ ⊕-sel ⊕-assoc ⊕-comm
-}
