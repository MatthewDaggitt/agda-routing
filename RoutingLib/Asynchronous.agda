open import Algebra.FunctionProperties using (Congruent₁)
open import Level using (_⊔_) renaming (zero to lzero; suc to lsuc)
open import Data.Fin using (Fin)
open import Data.Fin.Dec using (_∈?_)
open import Data.Fin.Properties using () renaming (setoid to 𝔽ₛ)
open import Data.Nat using (ℕ; _≤_; _+_; s≤s; _<_; zero; suc)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (∃; _×_; _,_)
--open import Relation.Binary.Indexed using (Setoid)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Unary using () renaming (_∈_ to _∈ᵤ_)
open import Induction.WellFounded using (Acc; acc)
open import Induction.Nat using (<-wellFounded)

open import RoutingLib.Data.Nat.Properties using (ℕₛ)
open import RoutingLib.Data.Fin.Properties using ()
open import RoutingLib.Data.Table using (Table)
import RoutingLib.Data.Table.Relation.Equality as TableEquality
open import RoutingLib.Relation.Binary.Indexed.Homogeneous -- as IndexedTypes
open import RoutingLib.Relation.Unary.Indexed

open import RoutingLib.Asynchronous.Schedule using (Schedule; 𝕋)

module RoutingLib.Asynchronous where

------------------------------------------------------------------------
-- Parallelisable functions

record Parallelisation {a ℓ n} (𝕊 : Setoid (Fin n) a ℓ) : Set (lsuc a ⊔ ℓ) where

  -- open IndexedTypes 𝕊ᵢ public
  open Setoid 𝕊 public renaming
    ( Carrierᵢ      to Sᵢ
    ; Carrier       to S
    ; reflᵢ         to ≈ᵢ-refl
    ; symᵢ          to ≈ᵢ-sym
    ; transᵢ        to ≈ᵢ-trans
    ; refl          to ≈-refl
    ; sym           to ≈-sym
    ; trans         to ≈-trans
    ; isEquivalence to ≈-isEquivalence
    )

  open Schedule

  field
    F      : (∀ i → Sᵢ i) → ∀ i → Sᵢ i
    F-cong : Congruent₁ _≈_ F


  asyncIter' : Schedule n → S → ∀ {t} → Acc _<_ t → S
  asyncIter' 𝓢 x[0] {zero}  _        i = x[0] i
  asyncIter' 𝓢 x[0] {suc t} (acc rs) i with i ∈? α 𝓢 (suc t)
  ... | yes _ = F (λ j → asyncIter' 𝓢 x[0] (rs (β 𝓢 (suc t) i j) (s≤s (causality 𝓢 t i j))) j) i
  ... | no  _ = asyncIter' 𝓢 x[0] (rs t ≤-refl) i

  asyncIter : Schedule n → S → 𝕋 → S
  asyncIter 𝓢 x[0] t = asyncIter' 𝓢 x[0] (<-wellFounded t)

  syncIter : S → ℕ → S
  syncIter x₀ zero     = x₀
  syncIter x₀ (suc K)  = F (syncIter x₀ K)

-------------------------------------------------------------------------
-- Safeness of parallelisations

module _ {a ℓ n} {𝕊 : Setoid (Fin n) a ℓ} (P : Parallelisation 𝕊) where

  open Parallelisation P

  -- P is a well behaved on the set of inputs V.
  record IsPartiallyAsynchronouslySafe {v} (V : Pred Sᵢ v) : Set (lsuc (a ⊔ ℓ) ⊔ v) where
    field
      m*         : S
      m*-reached : ∀ {x₀} → x₀ ∈ V → ∀ s → ∃ λ tᶜ → ∀ t → asyncIter s x₀ (tᶜ + t) ≈ m*

  -- P is a well behaved on all inputs.
  record IsAsynchronouslySafe : Set (lsuc (a ⊔ ℓ)) where
    field
      m*         : S
      m*-reached : ∀ X s → ∃ λ tᶜ → ∀ t → asyncIter s X (tᶜ + t) ≈ m*


-------------------------------------------------------------------------
-- Reachability

module _ {a ℓ n} {𝕊 : Setoid (Fin n) a ℓ} (P : Parallelisation 𝕊) where


-------------------------------------------------------------------------
-- Bisimilarity

module _ {a₁ a₂ ℓ₁ ℓ₂ n} {𝕊₁ : Setoid (Fin n) a₁ ℓ₁} {𝕊₂ : Setoid (Fin n) a₂ ℓ₂} where

  record Bisimilar (P : Parallelisation 𝕊₁) (Q : Parallelisation 𝕊₂) : Set (a₁ ⊔ a₂ ⊔ ℓ₁ ⊔ ℓ₂) where

    private
      module P = Parallelisation P
      module Q = Parallelisation Q
    
    field
      toᵢ      : ∀ {i} → P.Sᵢ i → Q.Sᵢ i
      fromᵢ    : ∀ {i} → Q.Sᵢ i → P.Sᵢ i

      toᵢ-cong : ∀ {i} {x y : P.Sᵢ i} → x P.≈ᵢ y → toᵢ x Q.≈ᵢ toᵢ y
      toᵢ-F    : ∀ {i} (x : P.S) → toᵢ (P.F x i) Q.≈ᵢ Q.F (λ j → toᵢ (x j)) i
      toᵢ-fromᵢ : ∀ {i} (x : Q.Sᵢ i) → toᵢ (fromᵢ x) Q.≈ᵢ x
      
    to : P.S → Q.S
    to x i = toᵢ (x i)

    from : Q.S → P.S
    from x i = fromᵢ (x i)
    
    
