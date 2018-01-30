open import Level using (Level; _⊔_) renaming (zero to lzero; suc to lsuc)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Product using (∃)
open import Relation.Binary using (Setoid; Decidable)

open import RoutingLib.Asynchronous
open import RoutingLib.Data.Nat.Properties using (ℕₛ)
open import RoutingLib.Data.Table using (Table; max)

module RoutingLib.Asynchronous.Theorems.Core {a ℓ n} {S : Table (Setoid a ℓ) n}
                                        (P : Parallelisation S) where

  open Parallelisation P
  open import RoutingLib.Function.Distance using (IsUltrametric)
  open import RoutingLib.Function.Distance M-setoid using (_StrContrOver_; _ContrOver_; Bounded)
  
  record ACO p : Set (a ⊔ lsuc p ⊔ ℓ) where
    field
      T            : ℕ
      D            : ℕ → Pred p
      D-subst      : ∀ K {x y} → x ≈ y → x ∈ D K → y ∈ D K
      D-decreasing : ∀ K → D (suc K) ⊆ D K
      D-finish     : ∃ λ ξ → ∀ K → Singleton-t ξ (D (T + K))
      f-monotonic  : ∀ K {t} → t ∈ D K → f t ∈ D (suc K)

  -- A version of ACO where the first box contains every element
  record TotalACO p : Set (a ⊔ lsuc p ⊔ ℓ) where
    field
      aco   : ACO p
      total : ∀ x → x ∈ ACO.D aco zero

    open ACO aco public

  record UltrametricConditions : Set (a ⊔ ℓ) where
    field
      dᵢ                 : ∀ {i} → Mᵢ i → Mᵢ i → ℕ

    d : M → M → ℕ
    d m n = max 0 (λ i → dᵢ {i} (m i) (n i))

    field
      dᵢ-isUltrametric   : ∀ {i} → IsUltrametric (S i) dᵢ
      f-strContr         : f StrContrOver d
      d-bounded          : Bounded d
      
      element            : M
      f-cong             : ∀ {x y} → x ≈ y → f x ≈ f y
      _≟_                : Decidable _≈_
