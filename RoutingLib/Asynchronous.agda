open import Algebra.FunctionProperties using (Congruent₁)
open import Level using (_⊔_) renaming (zero to lzero; suc to lsuc)
open import Data.Fin using (Fin)
open import Data.Fin.Dec using (_∈?_)
open import Data.Fin.Properties using () renaming (setoid to 𝔽ₛ)
open import Data.Maybe using (Maybe; just; nothing; Eq)
open import Data.Nat using (ℕ; _≤_; _+_; s≤s; _<_; zero; suc)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (∃; _×_; _,_)
open import Relation.Binary using (Rel)
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
open import RoutingLib.Relation.Binary.Indexed.Homogeneous
open import RoutingLib.Relation.Unary.Indexed

open import RoutingLib.Asynchronous.Schedule

module RoutingLib.Asynchronous where

------------------------------------------------------------------------
-- Parallelisable functions

record IsParallelisation {a n ℓ} {Sᵢ : Fin n → Set a} (_≈ᵢ_ : IRel Sᵢ ℓ)
                         (F : Epoch → (∀ i → Maybe (Sᵢ i)) → (∀ i → Maybe (Sᵢ i)))
                         : Set (a ⊔ ℓ) where
  field
    isEquivalenceᵢ : IsIndexedEquivalence Sᵢ _≈ᵢ_

  S : Set _
  S = ∀ i → Sᵢ i

  Sᵐᵢ : Fin n → Set _
  Sᵐᵢ i = Maybe (Sᵢ i)

  Sᵐ : Set _
  Sᵐ = ∀ i → Sᵐᵢ i

  toSᵐ : S → Sᵐ
  toSᵐ x i = just (x i)
  
  module _ (𝓢 : Schedule n) where
    open Schedule 𝓢

    -- The six cases (in-order)
    -- 1. Initially: not participating
    -- 2. Initially: participating
    -- 3. Currently: not participating
    -- 4. Currently: just started participating
    -- 5. Currently: participating but inactive
    -- 6. Currently: participating and active
    asyncIter' : S → ∀ {t} → Acc _<_ t → Sᵐ
    asyncIter' x₀ {zero} _ i with i ∈? ρ 0
    ... | no  _ = nothing
    ... | yes _ = just (x₀ i)  
    asyncIter' x₀ {suc t} (acc rec) i with i ∈? ρ (suc t) | i ∈? ρ t | i ∈? α (suc t)
    ... | no _  | _     | _     = nothing
    ... | yes _ | no  _ | _     = just (x₀ i)
    ... | yes _ | yes _ | no  _ = asyncIter' x₀ (rec t ≤-refl) i
    ... | yes _ | yes _ | yes _ = F (η t) (λ j → asyncIter' x₀ (rec (β (suc t) i j) (s≤s (β-causality t i j))) j) i

    asyncIter : S → 𝕋 → Sᵐ
    asyncIter x₀ t = asyncIter' x₀ (<-wellFounded t)

    {-
    syncIter : Epoch → S → ℕ → S
    syncIter e x₀ zero     = x₀
    syncIter e x₀ (suc K)  = F e (syncIter x₀ K)
    -}

  _≈_ : Rel Sᵐ (a ⊔ ℓ)
  x ≈ y = ∀ i → Eq _≈ᵢ_ (x i) (y i)
  
  open IsIndexedEquivalence isEquivalenceᵢ public renaming
    ( reflᵢ         to ≈ᵢ-refl
    ; symᵢ          to ≈ᵢ-sym
    ; transᵢ        to ≈ᵢ-trans
    ; refl          to ≈-refl
    ; sym           to ≈-sym
    ; trans         to ≈-trans
    ; isEquivalence to ≈-isEquivalence
    )

record Parallelisation a ℓ n : Set (lsuc a ⊔ lsuc ℓ) where
  field
    Sᵢ                : Fin n → Set a
    _≈ᵢ_              : IRel Sᵢ ℓ
    F                 : Epoch → (∀ i → Maybe (Sᵢ i)) → (∀ i → Maybe (Sᵢ i))
    isParallelisation : IsParallelisation _≈ᵢ_ F

  open IsParallelisation isParallelisation public
  
-------------------------------------------------------------------------
-- Safeness of parallelisations

module _ {a ℓ n} (P : Parallelisation a ℓ n) where

  open Parallelisation P

  -- P is well behaved on the set of inputs V.
  record IsPartiallyAsynchronouslySafe {v} (V : IPred Sᵢ v) : Set (lsuc (a ⊔ ℓ) ⊔ v) where
    field
      m*         : Sᵐ
      m*-reached : ∀ {x₀} → x₀ ∈ V → ∀ s → ∃ λ tᶜ → ∀ t → asyncIter s x₀ (tᶜ + t) ≈ m*

  IsAsynchronouslySafe : Set (lsuc (a ⊔ ℓ))
  IsAsynchronouslySafe = IsPartiallyAsynchronouslySafe (U Sᵢ)

{-
-------------------------------------------------------------------------
-- Bisimilarity

module _ {a₁ a₂ ℓ₁ ℓ₂ n} {𝕊₁ : IndexedSetoid (Fin n) a₁ ℓ₁} {𝕊₂ : IndexedSetoid (Fin n) a₂ ℓ₂} where

  record Bisimilar (P : Parallelisation 𝕊₁) (Q : Parallelisation 𝕊₂) : Set (a₁ ⊔ a₂ ⊔ ℓ₁ ⊔ ℓ₂) where

    private
      module P = Parallelisation P
      module Q = Parallelisation Q
    
    field
      toᵢ      : ∀ {i} → P.Sᵢ i → Q.Sᵢ i
      fromᵢ    : ∀ {i} → Q.Sᵢ i → P.Sᵢ i
      
      F-cong  : Congruent₁ Q._≈_ Q.F

      toᵢ-cong : ∀ {i} {x y : P.Sᵢ i} → x P.≈ᵢ y → toᵢ x Q.≈ᵢ toᵢ y
      toᵢ-fromᵢ : ∀ {i} (x : Q.Sᵢ i) → toᵢ (fromᵢ x) Q.≈ᵢ x
      toᵢ-F    : ∀ {i} (x : P.S) → toᵢ (P.F x i) Q.≈ᵢ Q.F (λ j → toᵢ (x j)) i
      
    to : P.S → Q.S
    to x i = toᵢ (x i)

    from : Q.S → P.S
    from x i = fromᵢ (x i)
-}
