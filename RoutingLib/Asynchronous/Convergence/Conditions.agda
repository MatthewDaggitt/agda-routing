open import Level using (_⊔_) renaming (suc to lsuc)
open import Data.Fin using (Fin)
open import Data.Nat using (ℕ; zero; suc; _+_; _<_)
open import Data.Product using (∃; ∃₂)
open import Relation.Binary using (Rel; Setoid; Decidable; _Preserves_⟶_)

open import RoutingLib.Asynchronous
open import RoutingLib.Data.Table using (Table; max)
open import RoutingLib.Data.Table.Relation.Pointwise using (Pointwise)
open import RoutingLib.Function.Metric using (IsUltrametric)

module RoutingLib.Asynchronous.Convergence.Conditions
  {a ℓ n} {𝕊ᵢ : Table (Setoid a ℓ) n}
  (𝓟 : Parallelisation 𝕊ᵢ)
  where

  open Parallelisation 𝓟
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
      D-decreasing : ∀ K → D (suc K) ⊆ D K
      D-finish     : ∃₂ λ T ξ → ∀ K → IsSingleton ξ (D (T + K))
      F-monotonic  : ∀ K {t} → t ∈ D K → F t ∈ D (suc K)


  -- A version of ACO where the first box contains every element
  record TotalACO p : Set (a ⊔ lsuc p ⊔ ℓ) where
    open ACO
    
    field
      aco   : ACO p
      total : ∀ x → x ∈ D aco 0

    open ACO aco public
    
  ------------------------
  -- Ultrametric spaces --
  ------------------------
  -- Ultrametic space conditions that are also sufficient (and necessary)
  -- conditions as defined by Gurney
  record UltrametricConditions : Set (a ⊔ ℓ) where
    field
      dᵢ                 : ∀ {i} → Sᵢ i → Sᵢ i → ℕ

    d : S → S → ℕ
    d x y = max 0 (λ i → dᵢ (x i) (y i))

    field
      dᵢ-isUltrametric    : ∀ {i} → IsUltrametric (𝕊ᵢ i) dᵢ
      F-strContrOnOrbits  : F StrContrOnOrbitsOver d
      F-strContrOnFP      : F StrContrOnFixedPointOver d
      d-bounded           : Bounded d

      element             : S
      _≟_                 : Decidable _≈_
      F-cong              : F Preserves _≈_ ⟶ _≈_



  ---------------------------------
  -- Other sufficient conditions --
  ---------------------------------
  -- Sufficient but not necessary conditions by Üresin and Dubois
  
  record StartingConditions p : Set (lsuc (a ⊔ ℓ ⊔ p)) where
    field
      D₀         : ∀ i → Sᵢ i → Set p
      D₀-closed  : ∀ x → x ∈ D₀ → F x ∈ D₀


  record SynchronousConditions p : Set (lsuc (a ⊔ ℓ ⊔ p)) where
    field
      start            : StartingConditions p
      poset            : M-poset p

    open StartingConditions start public
    open M-poset poset public
    
    field
      F-monotone       : ∀ {x y} → x ∈ D₀ → y ∈ D₀ → x ≼ y → F x ≼ F y
      iter-decreasing  : ∀ {x} → x ∈ D₀ → ∀ K → syncIter x (suc K) ≼ syncIter x K
      iter-converge    : ∀ {x} → x ∈ D₀ → ∃ λ T → ∀ t → syncIter x T ≈ syncIter x (T + t)



  record FiniteConditions p : Set (lsuc (a ⊔ ℓ ⊔ p)) where
    field
      start           : StartingConditions p
      poset           : M-poset p
      _≟_             : Decidable _≈_

    open StartingConditions start public
    open M-poset poset public

    field
      D₀-finite       : Finite-Pred D₀
      F-nonexpansive  : ∀ {x} → x ∈ D₀ → F x ≼ x
      F-monotone      : ∀ {x y} → x ∈ D₀ → y ∈ D₀ → x ≼ y → F x ≼ F y
      F-cong          : ∀ {x y} → x ≈ y → F x ≈ F y
