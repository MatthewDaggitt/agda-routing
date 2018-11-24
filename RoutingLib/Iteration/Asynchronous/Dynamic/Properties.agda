open import Level using (_⊔_) renaming (zero to lzero; suc to lsuc)
open import Data.Fin using (Fin)
open import Data.Fin.Dec using (_∈?_)
open import Data.Fin.Subset using (_∉_)
open import Data.Nat using (ℕ; _≤_; _+_; s≤s; _<_; zero; suc)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (∃; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Unary using (Pred; Universal) renaming (_∈_ to _∈ᵤ_)
open import Induction.WellFounded using (Acc; acc)
open import Induction.Nat using (<-wellFounded)

open import RoutingLib.Data.Nat.Properties using (ℕₛ)
open import RoutingLib.Data.Fin.Properties using ()
open import RoutingLib.Data.Table using (Table)
import RoutingLib.Data.Table.Relation.Equality as TableEquality
open import RoutingLib.Relation.Binary.Indexed.Homogeneous
open import RoutingLib.Relation.Unary.Indexed using (IPred; _∈_)

open import RoutingLib.Iteration.Asynchronous.Dynamic
open import RoutingLib.Iteration.Asynchronous.Dynamic.Schedule

module RoutingLib.Iteration.Asynchronous.Dynamic.Properties where

-------------------------------------------------------------------------
-- Basic properties of the asynchronous state function

module _ {a ℓ n} (𝓘 : AsyncIterable a ℓ n) (𝓢 : Schedule n) where

  open AsyncIterable 𝓘
  open Schedule 𝓢
  
  asyncIter-cong : ∀ x₀ {t₁ t₂} (acc₁ : Acc _<_ t₁) (acc₂ : Acc _<_ t₂) →
                   t₁ ≡ t₂ → asyncIter' 𝓘 𝓢 x₀ acc₁ ≈ asyncIter' 𝓘 𝓢 x₀ acc₂
  asyncIter-cong  x₀ {zero} rec₁ rec₂ refl i with i ∈? ρ 0
  ... | no  _ = ≈ᵢ-refl
  ... | yes _ = ≈ᵢ-refl
  asyncIter-cong x₀ {suc t} (acc rec₁) (acc rec₂) refl i with i ∈? ρ (suc t) | i ∈? ρ t | i ∈? α (suc t)
  ... | no _       | _     | _     = ≈ᵢ-refl
  ... | yes _      | no  _ | _     = ≈ᵢ-refl
  ... | yes _      | yes _ | no  _ = asyncIter-cong x₀ (rec₁ t _) _ refl i
  ... | yes i∈ρ₁₊ₜ | yes _ | yes _ = F-cong (η (suc t)) (ρ (suc t)) (λ {j} _ → asyncIter-cong x₀ (rec₁ (β (suc t) i j) _) _ refl j) i∈ρ₁₊ₜ

  -- If a node is inactive at time t then it has the blank state
  asyncIter-inactive : ∀ x₀ {t} (rec : Acc _<_ t) {i} →
                       i ∉ ρ t → asyncIter' 𝓘 𝓢 x₀ rec i ≡ ⊥ i
  asyncIter-inactive x₀ {zero} rec {i} i∉ρ₀ with i ∈? ρ 0
  ... | no  _    = refl
  ... | yes i∈ρ₀ = contradiction i∈ρ₀ i∉ρ₀
  asyncIter-inactive x₀ {suc t} (acc rec) {i} i∉ρ₁₊ₜ with i ∈? ρ (suc t)
  ... | no  _      = refl
  ... | yes i∈ρ₁₊ₜ = contradiction i∈ρ₁₊ₜ i∉ρ₁₊ₜ
  
-------------------------------------------------------------------------
-- Basic properties of safety

convergentOver-universal : ∀ {a ℓ p} {𝓘 : AsyncIterable a ℓ p}
                       {q} {X : IPred _ q} → (∀ x → x ∈ X) →
                       ConvergentOver 𝓘 X →
                       Convergent 𝓘
convergentOver-universal univ convergentOver = record
  { x*         = x*
  ; x*-fixed   = x*-fixed
  ; x*-reached = λ {x₀} _ → x*-reached (univ x₀)
  }
  where open ConvergentOver convergentOver


{-
-- The safe set can always be shrunk
shrinkSafety : ∀ {a ℓ n} {𝓘 : AsyncIterable a ℓ n} → 
               ∀ {v} {V : Pred Sᵢ v} {W : Pred Sᵢ v} →
               _⊆_ {A = Sᵢ} W V →
               IsPartiallyAsynchronouslySafe P V →
               IsPartiallyAsynchronouslySafe P W
shrinkSafety W⊆V V-safe = record
  { x*         = x*
  ; x*-reached = λ X∈W → x*-reached (W⊆V X∈W)
  }
  where open IsPartiallyAsynchronouslySafe V-safe
-}


{-
module _ {a ℓ n} where

  open IndexedSetoid 𝕊 using (_≈_) renaming (Carrierᵢ to Sᵢ; Carrier to S)
  
  shrinkSafety : ∀ {P : Parallelisation 𝕊} {v} {V : Pred Sᵢ v} {W : Pred Sᵢ v} →
                 _⊆_ {A = Sᵢ} W V →
                 IsPartiallyAsynchronouslySafe P V →
                 IsPartiallyAsynchronouslySafe P W
  shrinkSafety W⊆V V-safe = record
    { x*         = x*
    ; x*-reached = λ X∈W → x*-reached (W⊆V X∈W)
    }
    where open IsPartiallyAsynchronouslySafe V-safe

  
-}



