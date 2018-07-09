open import Level using (_⊔_) renaming (suc to lsuc)
open import Data.Fin using (Fin)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Product using (∃; ∃₂; _×_)
open import Data.List using (List)
import Data.List.Membership.Setoid as Membership
open import Relation.Binary using (Total; _Preserves_⟶_)
import Relation.Binary.NonStrictToStrict as NonStrictToStrict

open import RoutingLib.Asynchronous
open import RoutingLib.Data.Table using (Table; max)
open import RoutingLib.Data.Table.Relation.Pointwise using (Pointwise)
open import RoutingLib.Function.Metric using (IsUltrametric)
open import RoutingLib.Relation.Binary.Indexed.Homogeneous
open import RoutingLib.Relation.Unary.Indexed

module RoutingLib.Asynchronous.Convergence.Conditions
  {a ℓ n} {𝕊 : Setoid (Fin n) a ℓ}
  (𝓟 : Parallelisation 𝕊)
  where

  open Parallelisation 𝓟

  -----------------------------------------
  -- Asynchronously contracting operator --
  -----------------------------------------
  -- Sufficient (and necessary conditions) for convergence
  -- as defined by Üresin and Dubois
  record ACO p : Set (a ⊔ lsuc p ⊔ ℓ) where
    field
      D            : ℕ → Pred Sᵢ p
      D-decreasing : ∀ K → _⊆_ {A = Sᵢ} (D (suc K)) (D K)
      F-monotonic  : ∀ K {t} → t ∈ D K → F t ∈ D (suc K)
      D-finish     : ∃₂ λ T ξ → ∀ K → ξ ∈ D (T + K) × (∀ {x} → x ∈ D (T + K) → ξ ≈ x)


  ------------------------
  -- Ultrametric spaces --
  ------------------------
  -- Ultrametic space conditions that are also sufficient (and necessary)
  -- conditions as defined by Gurney
  
  open import RoutingLib.Function.Metric setoid
    using (Bounded; _StrContrOnOrbitsOver_; _StrContrOnFixedPointOver_)
    
  record UltrametricConditions : Set (a ⊔ ℓ) where
    field
      dᵢ                 : ∀ {i} → Sᵢ i → Sᵢ i → ℕ

    d : S → S → ℕ
    d x y = max 0 (λ i → dᵢ (x i) (y i))

    field
      dᵢ-isUltrametric    : ∀ {i} → IsUltrametric (Setoid 𝕊 at  i) dᵢ
      F-strContrOnOrbits  : F StrContrOnOrbitsOver d
      F-strContrOnFP      : F StrContrOnFixedPointOver d
      d-bounded           : Bounded d

      element             : S
      _≟ᵢ_                : Decidable Sᵢ _≈ᵢ_
      F-cong              : F Preserves _≈_ ⟶ _≈_


  ---------------------------------
  -- Other sufficient conditions --
  ---------------------------------
  -- Sufficient but not necessary conditions by Üresin and Dubois

  record SynchronousConditions p o : Set (lsuc (a ⊔ ℓ ⊔ p ⊔ o)) where
  
    field
      D₀               : Pred Sᵢ p
      D₀-cong          : ∀ {x y} → x ∈ D₀ → x ≈ y → y ∈ D₀
      D₀-closed        : ∀ {x} → x ∈ D₀ → F x ∈ D₀

      _≤ᵢ_              : Rel Sᵢ o
      ≤ᵢ-isPartialOrder : IsPartialOrder Sᵢ _≈ᵢ_ _≤ᵢ_

    open IsPartialOrder ≤ᵢ-isPartialOrder public
      renaming
      ( reflexive  to ≤-reflexive
      ; refl       to ≤-refl
      ; trans      to ≤-trans
      ; antisym    to ≤-antisym
      ; reflexiveᵢ to ≤ᵢ-reflexive
      ; reflᵢ      to ≤ᵢ-refl
      ; transᵢ     to ≤ᵢ-trans
      ; antisymᵢ   to ≤ᵢ-antisym
      )
    
    _≤_ = Lift Sᵢ _≤ᵢ_
    
    field
      ξ                : S
      ξ-fixed          : F ξ ≈ ξ
      F-monotone       : ∀ {x y} → x ∈ D₀ → y ∈ D₀ → x ≤ y → F x ≤ F y
      F-cong           : ∀ {x y} → x ≈ y → F x ≈ F y
      iter-decreasing  : ∀ {x} → x ∈ D₀ → ∀ K → syncIter x (suc K) ≤ syncIter x K
      iter-converge    : ∀ {x} → x ∈ D₀ → ∃ λ T → syncIter x T ≈ ξ




  record FiniteConditions p o : Set (lsuc (a ⊔ ℓ ⊔ p ⊔ o)) where
    open Membership (setoid) using () renaming (_∈_ to _∈L_)
    
    field
      D₀                : Pred Sᵢ p
      D₀-cong           : ∀ {x y} → x ∈ D₀ → x ≈ y → y ∈ D₀
      D₀-closed         : ∀ {x} → x ∈ D₀ → F x ∈ D₀
      D₀-finite         : ∃ λ xs → ∀ {x} → x ∈ D₀ → x ∈L xs
      
      -- ξ∈D₀              : ξ ∈ D₀
      
      _≤ᵢ_              : Rel Sᵢ o
      ≤ᵢ-isPartialOrder : IsPartialOrder Sᵢ _≈ᵢ_ _≤ᵢ_
      _≟ᵢ_              : Decidable Sᵢ _≈ᵢ_

    open IsPartialOrder ≤ᵢ-isPartialOrder public
      renaming
      ( reflexive  to ≤-reflexive
      ; refl       to ≤-refl
      ; trans      to ≤-trans
      ; antisym    to ≤-antisym
      ; reflexiveᵢ to ≤ᵢ-reflexive
      ; reflᵢ      to ≤ᵢ-refl
      ; transᵢ     to ≤ᵢ-trans
      ; antisymᵢ   to ≤ᵢ-antisym
      )

    _≤_ = Lift Sᵢ _≤ᵢ_
    open NonStrictToStrict _≈_ _≤_ using (_<_)
    
    field
      ξ               : S
      ξ∈D₀            : ξ ∈ D₀
      F-strictlyDecr  : ∀ {x} → x ∈ D₀ → x ≉ ξ → F x < x
      F-monotone      : ∀ {x y} → x ∈ D₀ → y ∈ D₀ → x ≤ y → F x ≤ F y
      F-cong          : ∀ {x y} → x ≈ y → F x ≈ F y
