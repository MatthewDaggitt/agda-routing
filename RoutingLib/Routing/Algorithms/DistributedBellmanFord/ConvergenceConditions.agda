open import Level using (_⊔_)
open import Data.Product using (_×_)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)
open import Algebra.FunctionProperties using (Associative; Commutative; LeftIdentity; RightIdentity; RightZero; Idempotent)

open import RoutingLib.Routing.Definitions
open import RoutingLib.Algebra.FunctionProperties using (Selective)
open import RoutingLib.Relation.Binary.RespectedBy using (_RespectedBy_)
open import RoutingLib.Data.List.Enumeration using (Enumeration)
open import RoutingLib.Algebra.Selectivity.Properties using (idem)

module RoutingLib.Routing.Algorithms.DistributedBellmanFord.ConvergenceConditions  where

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

      -- Annihilator
      one : Route
      one-anᵣ-⊕ : RightZero _≈_ one _⊕_




  -------------------
  -- Without paths --
  -------------------
  -- Sufficient conditions for the convergence of the synchronous
  -- Distributed Bellman Ford from any state when the algebra
  -- is not lexed with paths

  record ConvergenceConditions 
    {a b ℓ n} (rp : RoutingProblem a b ℓ n) : Set (a ⊔ b ⊔ ℓ) where
    
    open RoutingProblem rp
    
    field
      -- Special routes
      0# : Route

      -- Operator properties
      ⊕-assoc : Associative _≈_ _⊕_
      ⊕-sel   : Selective _≈_ _⊕_
      ⊕-comm  : Commutative _≈_ _⊕_
      ⊕-almost-strictly-absorbs-▷ : ∀ s {r} → r ≉ 0# → ((s ▷ r) ⊕ r ≈ r) × (r ≉ s ▷ r)

      0#-idᵣ-⊕ : RightIdentity _≈_ 0# _⊕_
      0#-anᵣ-▷ : ∀ s → s ▷ 0# ≈ 0#

      Iᵢᵢ-almost-anᵣ-⊕ : ∀ i s r → (s ▷ r) ⊕ I i i ≈ I i i
      Iᵢⱼ≈0# : ∀ {i j} → j ≢ i → I i j ≈ 0#

      -- Other properties
      routes-enumerable : Enumeration S


  
    -- Immediate properties

    ⊕-idem : Idempotent _≈_ _⊕_
    ⊕-idem = idem _≈_ _⊕_ ⊕-sel

    -- Natural orders

    open import RoutingLib.Algebra.Selectivity.NaturalOrders S _⊕_ ⊕-pres-≈ using () renaming (_≤ᵣ_ to _≤_; ≤ᵣ-respᵣ-≈ to ≤-respᵣ-≈; ≤ᵣ-respₗ-≈ to ≤-respₗ-≈) public
    open import RoutingLib.Algebra.Selectivity.NaturalOrders S _⊕_ ⊕-pres-≈ using () renaming (≤ᵣ-total to ass⇨≤-total; ≤ᵣ-poset to ass⇨≤-poset)

    _≤?_ : Decidable _≤_
    x ≤? y = y ⊕ x ≟ x  

    ≤-total : Total _≤_
    ≤-total = ass⇨≤-total ⊕-sel ⊕-comm

    ≤-poset : Poset b ℓ ℓ
    ≤-poset = ass⇨≤-poset ⊕-comm ⊕-assoc ⊕-idem

    open Poset ≤-poset using () renaming (refl to ≤-refl; trans to ≤-trans; antisym to ≤-antisym) public

    -- Identity matrix properties

    0#-idₗ-⊕ : LeftIdentity _≈_ 0# _⊕_
    0#-idₗ-⊕ x = trans (⊕-comm 0# x) (0#-idᵣ-⊕ x)

    Iᵢⱼ-idᵣ-⊕ : ∀ {i j} → j ≢ i → RightIdentity _≈_ (I i j) _⊕_
    Iᵢⱼ-idᵣ-⊕ {i} {j} j≢i x = trans (⊕-pres-≈ refl (Iᵢⱼ≈0# j≢i)) (0#-idᵣ-⊕ x)

    Iᵢⱼ-idₗ-⊕ : ∀ {i j} → j ≢ i → LeftIdentity _≈_ (I i j) _⊕_
    Iᵢⱼ-idₗ-⊕ {i} {j} j≢i x = trans (⊕-comm (I i j) x) (Iᵢⱼ-idᵣ-⊕ j≢i x)

    Iᵢⱼ-anᵣ-▷ : ∀ {i j} → j ≢ i → ∀ s → s ▷ I i j ≈ I i j
    Iᵢⱼ-anᵣ-▷ j≢i s = trans (trans (▷-pres-≈ s (Iᵢⱼ≈0# j≢i)) (0#-anᵣ-▷ s)) (sym (Iᵢⱼ≈0# j≢i))

    Iᵢⱼ≈Iₖₗ : ∀ {i j k l} → j ≢ i → l ≢ k → I i j ≈ I k l
    Iᵢⱼ≈Iₖₗ j≢i l≢k = trans (Iᵢⱼ≈0# j≢i) (sym (Iᵢⱼ≈0# l≢k))
