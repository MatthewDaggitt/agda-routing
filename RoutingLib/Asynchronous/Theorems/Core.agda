open import Level using (Level; _⊔_) renaming (zero to lzero; suc to lsuc)
open import Data.Fin using (Fin)
open import Data.Nat using (ℕ; zero; suc; _+_; _<_)
open import Data.Product using (∃; ∃₂)
open import Relation.Binary using (Rel; Setoid; Decidable; _Preserves_⟶_)

open import RoutingLib.Asynchronous
open import RoutingLib.Data.Nat.Properties using (ℕₛ)
open import RoutingLib.Data.Table using (Table; max)
open import RoutingLib.Data.Table.Relation.Pointwise using (Pointwise)
open import RoutingLib.Function.Image using (FiniteImage)
open import RoutingLib.Function.Metric using (IsUltrametric)
import RoutingLib.Function.Metric.FixedPoint as FixedPoints

module RoutingLib.Asynchronous.Theorems.Core {a ℓ n} {𝕊ᵢ : Table (Setoid a ℓ) n}
                                        (P : Parallelisation 𝕊ᵢ) where

  open Parallelisation P
  open import RoutingLib.Function.Metric 𝕊
    using (Bounded; _StrContrOnOrbitsOver_; _StrContrOnFixedPointOver_)

  -----------------------------------------
  -- Asynchronously contracting operator --
  -----------------------------------------
  -- Sufficient (and necessary conditions) for convergence
  -- as defined by Üresin and Dubois
  record ACO p : Set (a ⊔ lsuc p ⊔ ℓ) where
    field
      D            : ℕ → ∀ i → Sᵢ i → Set p
      -- D-subst      : ∀ K {x y} → x ≈ y → x ∈ D K → y ∈ D K
      D-decreasing : ∀ K → D (suc K) ⊆ D K
      D-finish     : ∃₂ λ T ξ → ∀ K → IsSingleton ξ (D (T + K))
      F-monotonic  : ∀ K {t} → t ∈ D K → F t ∈ D (suc K)

  -- A version of ACO where the first box contains every element
  record TotalACO p : Set (a ⊔ lsuc p ⊔ ℓ) where
    field
      aco   : ACO p

    open ACO aco public

    field
      total : ∀ x → x ∈ D 0
    
  ------------------------
  -- Ultrametric spaces --
  ------------------------
  -- Ultrametic space conditions that are also sufficient (and necessary)
  -- conditions as defined by Gurney
  record UltrametricConditions : Set (a ⊔ ℓ) where
    field
      dᵢ                 : ∀ {i} → Sᵢ i → Sᵢ i → ℕ

    d : S → S → ℕ
    d m n = max 0 (λ i → dᵢ {i} (m i) (n i))

    field
      dᵢ-isUltrametric  : ∀ {i} → IsUltrametric (𝕊ᵢ i) dᵢ
      F-strContrOrbits  : F StrContrOnOrbitsOver d
      F-strContrOnFP    : F StrContrOnFixedPointOver d
      d-bounded         : Bounded d

      element : S
      _≟_     : Decidable _≈_
      F-cong  : F Preserves _≈_ ⟶ _≈_



  ---------------------------------
  -- Other sufficient conditions --
  ---------------------------------
  -- Sufficient but not necessary conditions by Üresin and Dubois
  
  record Start p : Set (lsuc (a ⊔ ℓ ⊔ p)) where
    field
      x₀ : S
      D₀ : Pred p
      x₀∈D₀ : x₀ ∈ D₀
      D₀-subst : ∀ {x y} → x ≈ y → x ∈ D₀ → y ∈ D₀
      D₀-closed : ∀ x → x ∈ D₀ → F x ∈ D₀
  
  record SynchronousConditions p : Set (lsuc (a ⊔ ℓ ⊔ p)) where
    field
      start : Start p
      poset : M-poset p

    open Start start
    open M-poset poset
    
    field
      F-monotone      : ∀ {x y} → x ∈ D₀ → y ∈ D₀ → x ≼ y → F x ≼ F y
      iter-decreasing : ∀ K → syncIter x₀ (suc K) ≼ syncIter x₀ K
      iter-converge   : ∃ λ T → ∀ t → syncIter x₀ T ≈ syncIter x₀ (T + t)
      
  record FiniteConditions p : Set (lsuc (a ⊔ ℓ ⊔ p)) where
    field
      start : Start p
      poset : M-poset p
      _≟_   : Decidable _≈_

    open Start start
    open M-poset poset

    field
      D₀-finite       : Finite-Pred D₀
      F-nonexpansive  : ∀ {x} → x ∈ D₀ → F x ≼ x
      F-monotone      : ∀ {x y} → x ∈ D₀ → y ∈ D₀ → x ≼ y → F x ≼ F y
      F-cong          : ∀ {x y} → x ≈ y → F x ≈ F y
