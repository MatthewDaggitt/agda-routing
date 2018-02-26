open import Level using (_⊔_) renaming (suc to lsuc)
open import Data.Product using (Σ; ∃; ∃₂; _×_; _,_)
open import Data.Sum using (_⊎_)
open import Relation.Binary using (DecTotalOrder; _Preserves_⟶_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)
open import Relation.Nullary using (¬_; Dec)
open import Algebra.Structures using (IsSemigroup)
import Algebra.FunctionProperties as FunctionProperties

open import RoutingLib.Routing.Definitions
open import RoutingLib.Data.SimplePath
  using (SimplePath; []; _∷_∣_∣_; valid; invalid)
open import RoutingLib.Data.SimplePath.Relation.Equality
open import RoutingLib.Data.SimplePath.NonEmpty using (_⇿_; _∈_; _∉_)
import RoutingLib.Algebra.Selectivity.RightNaturalOrder as RightNaturalOrder
open import RoutingLib.Algebra.Selectivity.Properties using (idem)

module RoutingLib.Routing.BellmanFord.PathVector.SufficientConditions  where

  ----------------
  -- With paths --
  ----------------
  -- Sufficient conditions for the convergence of the synchronous
  -- Distributed Bellman Ford from any state when the algebra
  -- is lexed with paths

  record PathSufficientConditions
    {a b ℓ} {𝓡𝓐 : RoutingAlgebra a b ℓ}
    {n} (𝓡𝓟 : RoutingProblem 𝓡𝓐 n) : Set (a ⊔ lsuc b ⊔ lsuc ℓ) where

    open RoutingProblem 𝓡𝓟
    open FunctionProperties _≈_
    
    field
      -- Operator properties
      ⊕-assoc             : Associative _⊕_
      ⊕-sel               : Selective   _⊕_
      ⊕-comm              : Commutative _⊕_
      ⊕-strictlyAbsorbs-▷ : ∀ f {x} → x ≉ 0# → x <₊ f ▷ x

      -- Element properties
      ▷-zero     : ∀ f → f ▷ 0# ≈ 0#
      ⊕-zeroʳ     : RightZero 1# _⊕_
      ⊕-identityʳ : RightIdentity 0# _⊕_
      
      -- Path
      path           : ∀ r → SimplePath n
      path-cong      : path Preserves _≈_ ⟶ _≈ₚ_
      r≈1⇒path[r]≈[] : ∀ {r} → r ≈ 1# → path r ≈ₚ valid [] 
      r≈0⇒path[r]≈∅  : ∀ {r} → r ≈ 0# → path r ≈ₚ invalid
      path[r]≈∅⇒r≈0  : ∀ {r} → path r ≈ₚ invalid  → r ≈ 0#
      path-reject    : ∀ {i j r p} → path r ≈ₚ valid p → ¬ (i , j) ⇿ p ⊎ i ∈ p → A i j ▷ r ≈ 0#
      path-accept    : ∀ {i j r p} → path r ≈ₚ valid p → A i j ▷ r ≉ 0# →
                       ∀ ij⇿p i∉p → path (A i j ▷ r) ≈ₚ valid ((i , j) ∷ p ∣ ij⇿p ∣ i∉p)


    open RightNaturalOrder _≈_ _⊕_ using ()
      renaming (≤-decTotalOrder to ass⇨≤-decTotalOrder)

    ⊕-idem : Idempotent _⊕_
    ⊕-idem = idem _≈_ _⊕_ ⊕-sel
    
    ⊕-isSemigroup : IsSemigroup _≈_ _⊕_
    ⊕-isSemigroup = record
      { isEquivalence = ≈-isEquivalence
      ; assoc         = ⊕-assoc
      ; ∙-cong        = ⊕-cong
      }
    
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
