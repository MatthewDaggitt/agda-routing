
open import Level using (_⊔_) renaming (zero to lzero; suc to lsuc)
open import Data.Fin using (Fin)
open import Data.Fin.Dec using (_∈?_)
open import Data.Fin.Properties using () renaming (setoid to 𝔽ₛ)
open import Data.Nat using (ℕ; _≤_; _+_; s≤s; _<_; zero; suc)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (∃; _×_; _,_)
open import Relation.Binary using (DecSetoid; Setoid; Rel; _Preserves_⟶_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Unary using () renaming (_∈_ to _∈ᵤ_)
open import Induction.WellFounded using (Acc; acc)
open import Induction.Nat using (<-wellFounded)

open import RoutingLib.Data.Nat.Properties using (ℕₛ)
open import RoutingLib.Data.Fin.Properties using ()
open import RoutingLib.Asynchronous.Schedule using (Schedule; 𝕋)
open import RoutingLib.Data.Table using (Table)

import RoutingLib.Data.Table.Relation.Equality as TableEquality
import RoutingLib.Data.Table.IndexedTypes as IndexedTypes

module RoutingLib.Asynchronous where

------------------------------------------------------------------------
-- Parallelisable functions

record Parallelisation {a ℓ n} (𝕊ᵢ : Table (Setoid a ℓ) n) : Set (lsuc a) where

  open IndexedTypes 𝕊ᵢ public
  open Schedule

  field
    F      : S → S

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

module _ {a ℓ n} {𝕊ᵢ : Fin n → Setoid a ℓ} where

  open IndexedTypes 𝕊ᵢ
  
  -- A record capturing the idea that P is a well behaved on some inputs.
  record IsPartiallyAsynchronouslySafe
    (P : Parallelisation 𝕊ᵢ)         -- Parallelisation
    {v} (V : Pred v) -- Safe inputs
    : Set (lsuc (a ⊔ ℓ) ⊔ v) where

    open Parallelisation P using (asyncIter)

    field
      m*         : S
      m*-reached : ∀ {X} → X ∈ V → ∀ s → ∃ λ tᶜ → ∀ t → asyncIter s X (tᶜ + t) ≈ m*



  -- A record capturing the idea that P is a well behaved on all inputs.
  record IsAsynchronouslySafe
    (P : Parallelisation 𝕊ᵢ)  -- Parallelisation
    : Set (lsuc (a ⊔ ℓ)) where

    open Parallelisation P using (asyncIter)

    field
      m*         : S
      m*-reached : ∀ X s → ∃ λ tᶜ → ∀ t → asyncIter s X (tᶜ + t) ≈ m*


  shrinkSafety : ∀ {P v} {V : Pred v} {W : Pred v} →
                 W ⊆ V →
                 IsPartiallyAsynchronouslySafe P V →
                 IsPartiallyAsynchronouslySafe P W
  shrinkSafety W⊆V V-safe = record
    { m*         = m*
    ; m*-reached = λ X∈W → m*-reached (W⊆V X∈W)
    }
    where open IsPartiallyAsynchronouslySafe V-safe
    
  partialToTotalSafety : ∀ {P v} {V : Pred v}  →
                         (∀ x → x ∈ V) → 
                         IsPartiallyAsynchronouslySafe P V →
                         IsAsynchronouslySafe P
  partialToTotalSafety total partiallySafe = record
    { m*         = m*
    ; m*-reached = λ X → m*-reached (total X)
    }
    where open IsPartiallyAsynchronouslySafe partiallySafe



-- The empty computation is safe (phew!)
0-IsSafe : ∀ {a ℓ} {T : Fin 0 → Setoid a ℓ} (P : Parallelisation T) →
           IsAsynchronouslySafe P
0-IsSafe p = record { m* = λ() ; m*-reached = λ _ _ → 0 , λ _ () }


