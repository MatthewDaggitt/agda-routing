open import Level using (_⊔_) renaming (zero to lzero; suc to lsuc)
open import Data.Fin using (Fin)
open import Data.Fin.Dec using (_∈?_)
open import Data.Fin.Properties using () renaming (setoid to 𝔽ₛ)
open import Data.Nat using (ℕ; _≤_; _+_; s≤s; _<_; zero; suc)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (∃; _×_)
open import Relation.Binary using (DecSetoid; Setoid; Rel; _Preserves_⟶_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Unary using (Pred) renaming (_∈_ to _∈ᵤ_)
open import Induction.WellFounded using (Acc; acc)
open import Induction.Nat using (<-well-founded)

open import RoutingLib.Data.Nat.Properties using (ℕₛ)
open import RoutingLib.Data.Fin.Properties using ()
open import RoutingLib.Asynchronous.Schedule using (Schedule; 𝕋)
open import RoutingLib.Data.Table using (Table)

import RoutingLib.Data.Table.Relation.Equality as TableEquality
import RoutingLib.Data.Table.IndexedTypes as IndexedTypes
module RoutingLib.Asynchronous where

  -----------------------
  -- Parallel function --
  -----------------------
  -- An operation σ that can be decomposed and carried out on n separate processors 
  record Parallelisation {a ℓ n} (S : Table (Setoid a ℓ) n) : Set (lsuc a) where

    open IndexedTypes S public
    
    field
      f      : M → M

    module _ (𝕤 : Schedule n) (x₀ : M) where

      open Schedule 𝕤

      async-iter' : ∀ {t} → Acc _<_ t → M
      async-iter' {zero}  _        i = x₀ i
      async-iter' {suc t} (acc rs) i with i ∈? α (suc t)
      ... | yes _ = f (λ j → async-iter' (rs (β (suc t) i j) (s≤s (causality t i j))) j) i
      ... | no  _ = async-iter' (rs t ≤-refl) i

      async-iter : 𝕋 → M
      async-iter t = async-iter' (<-well-founded t)



  -- A record encapsulating the idea that p is a well behaved parallelisation
  record IsAsynchronouslySafe {a ℓ n} {S : Fin n → Setoid a ℓ}
                              (p : Parallelisation S) : Set (lsuc (a ⊔ ℓ)) where
  
    open Parallelisation p
    
    field
      m*         : M
      m*-reached : ∀ s X → ∃ λ tᶜ → ∀ t → async-iter s X (tᶜ + t) ≈ m*
