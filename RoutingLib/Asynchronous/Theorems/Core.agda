open import Level using (Level; _⊔_) renaming (zero to lzero; suc to lsuc)
open import Data.Fin using (Fin)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Product using (∃)
open import Relation.Binary using (Rel; Setoid; Decidable)

open import RoutingLib.Asynchronous
open import RoutingLib.Data.Nat.Properties using (ℕₛ)
open import RoutingLib.Data.Table using (Table; max)
open import RoutingLib.Data.Table.Relation.Pointwise using (Pointwise)
open import RoutingLib.Function.Image using (FiniteImage)

module RoutingLib.Asynchronous.Theorems.Core {a ℓ n} {S : Table (Setoid a ℓ) n}
                                        (P : Parallelisation S) where

  open Parallelisation P
  open import RoutingLib.Function.Distance using (IsUltrametric)
  open import RoutingLib.Function.Distance M-setoid using (_StrContrOver_)
  
  record ACO p : Set (lsuc (lsuc (a ⊔ p ⊔ ℓ))) where
    field
      D            : ℕ → Pred p
      D-subst      : ∀ K {x y} → x ≈ y → x ∈ D K → y ∈ D K
      D-decreasing : ∀ K → D (suc K) ⊆ D K
      D-finish     : ∃ λ T → ∃ λ ξ → ∀ K → Singleton-t ξ (D (T + K))
      f-monotonic  : ∀ K {t} → t ∈ D K → f t ∈ D (suc K)


  record UltrametricConditions : Set (a ⊔ ℓ) where
    field
      dᵢ                 : ∀ {i} → Mᵢ i → Mᵢ i → ℕ

    d : M → M → ℕ
    d m n = max 0 (λ i → dᵢ {i} (m i) (n i))

    field
      element           : M
      dᵢ-isUltrametric  : ∀ {i} → IsUltrametric (S i) dᵢ
      f-strContrOver-d  : f StrContrOver d
      
      f-cong            : ∀ {x y} → x ≈ y → f x ≈ f y
      _≟_               : Decidable _≈_
      d-finiteImage     : ∀ (m : M) → FiniteImage ℕₛ (d m)


  record Start p : Set (lsuc (a ⊔ ℓ ⊔ p)) where
    field
      x₀ : M
      D₀ : Pred p
      x₀∈D₀ : x₀ ∈ D₀
      D₀-subst : ∀ {x y} → x ≈ y → x ∈ D₀ → y ∈ D₀
      D₀-closed : ∀ x → x ∈ D₀ → f x ∈ D₀

  iter : M → ℕ → M
  iter x₀ zero     = x₀
  iter x₀ (suc K)  = f (iter x₀ K)

  record SynchronousConditions p : Set (lsuc (a ⊔ ℓ ⊔ p)) where
    field
      start : Start p
      poset : M-poset p

    open Start start
    open M-poset poset
    
    field
      f-monotone      : ∀ {x y} → x ∈ D₀ → y ∈ D₀ → x ≼ y → f x ≼ f y
      iter-decreasing : ∀ K → iter x₀ (suc K) ≼ iter x₀ K
      iter-converge   : ∃ λ T → ∀ t → iter x₀ T ≈ iter x₀ (T + t)
      
  record FiniteConditions p : Set (lsuc (a ⊔ ℓ ⊔ p)) where
    field
      start : Start p
      poset : M-poset p
      _≟_   : Decidable _≈_

    open Start start
    open M-poset poset

    field
      D₀-finite       : Finite-Pred D₀
      f-nonexpansive  : ∀ {x} → x ∈ D₀ → f x ≼ x
      f-monotone      : ∀ {x y} → x ∈ D₀ → y ∈ D₀ → x ≼ y → f x ≼ f y
      f-cong : ∀ {x y} → x ≈ y → f x ≈ f y
      
