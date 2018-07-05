open import Data.Fin using (Fin; zero; suc)
open import Data.Nat using (zero; suc; _+_)
open import Data.Product
open import Level using () renaming (zero to ℓ₀)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Unary using (U)
open import Relation.Unary.Properties using (U-Universal)

open import RoutingLib.Data.Table using (Table)
import RoutingLib.Data.Table.IndexedTypes as IndexedTypes
open import RoutingLib.Asynchronous
open import RoutingLib.Asynchronous.Convergence.Conditions using (SynchronousConditions)

module RoutingLib.Asynchronous.Examples.Proposition3_Counterexample where


  data S : Set where
    a : S
    b : S

  module _ where

    -- abstract

    data _≤_ : Rel S ℓ₀ where
      ≤-refl : ∀ {s} → s ≤ s

    ≤-isPartialOrder : IsPartialOrder _≡_ _≤_
    ≤-isPartialOrder = record
      { isPreorder = record
        { isEquivalence = isEquivalence
        ; reflexive = λ { refl → ≤-refl }
        ; trans = λ { ≤-refl ≤-refl → ≤-refl }
        }
      ; antisym = λ { ≤-refl _ → refl }
      }

  

  F : Table S 1 → Table S 1
  F x = x

  𝕊ᵢ : Table (Setoid _ _) 1
  𝕊ᵢ i = setoid S

  
  F∥ : Parallelisation 𝕊ᵢ
  F∥ = record { F = F }

  open Parallelisation F∥ hiding (F)

  poset : M-poset _
  poset = record
    { _≼ᵢ_            = _≤_
    ; isPartialOrderᵢ = λ _ → ≤-isPartialOrder
    }

  open M-poset poset using (_≼_)

  D₀ : Pred _
  D₀ i = U

  D₀-closed : ∀ s → s ∈ D₀ → F s ∈ D₀
  D₀-closed s s∈D₀ i = U-Universal (s i)

  F-monotone : ∀ {x y} → x ∈ D₀ → y ∈ D₀ → x ≼ y → F x ≼ F y
  F-monotone _ _ x≼y i = x≼y i

  syncIter-id : ∀ x t i → x i ≡ syncIter x t i
  syncIter-id x zero    i = refl
  syncIter-id x (suc t) i = syncIter-id x t i
  
  iter-decreasing : ∀ {x} → x ∈ D₀ → ∀ K → syncIter x (suc K) ≼ syncIter x K
  iter-decreasing _ K i = ≤-refl

  iter-converge : ∀ {x} → x ∈ D₀ → ∃ λ T → ∀ t → syncIter x T ≈ syncIter x (T + t)
  iter-converge {x} _ = 0 , syncIter-id x
  
  syncConditions : SynchronousConditions F∥ _
  syncConditions = record
    { start           = record
      { D₀        = D₀
      ; D₀-closed = D₀-closed
      }
    ; poset           = poset
    ; F-monotone      = F-monotone
    ; iter-decreasing = iter-decreasing
    ; iter-converge   = iter-converge
    }
  
 
  -- But

  a-convergesTo-a : F (λ _ → a) ≡ (λ _ → a)
  a-convergesTo-a = refl

  b-convergesTo-b : F (λ _ → b) ≡ (λ _ → b)
  b-convergesTo-b = refl
