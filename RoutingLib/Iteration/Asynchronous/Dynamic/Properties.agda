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
open import RoutingLib.Iteration.Asynchronous.Schedule

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

-- The empty computation is safe
0-IsSafe : ∀ {a ℓ} (𝓘 : AsyncIterable a ℓ 0) → IsSafe 𝓘
0-IsSafe p = record
  { m*         = λ _ _ ()
  ; m*-reached = λ _ _ → 0 , λ _ _ ()
  }

isSafeOver-universal : ∀ {a ℓ p} {𝓘 : AsyncIterable a ℓ p}
                       {q} {X : IPred _ q} → (∀ x → x ∈ X) →
                       IsSafeOver 𝓘 X →
                       IsSafe 𝓘
isSafeOver-universal univ safeOver = record
  { m*         = m*
  ; m*-reached = λ {x₀} _ → m*-reached (univ x₀)
  }
  where open IsSafeOver safeOver







{-
-- The safe set can always be shrunk
shrinkSafety : ∀ {a ℓ n} {𝓘 : AsyncIterable a ℓ n} → 
               ∀ {v} {V : Pred Sᵢ v} {W : Pred Sᵢ v} →
               _⊆_ {A = Sᵢ} W V →
               IsPartiallyAsynchronouslySafe P V →
               IsPartiallyAsynchronouslySafe P W
shrinkSafety W⊆V V-safe = record
  { m*         = m*
  ; m*-reached = λ X∈W → m*-reached (W⊆V X∈W)
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
    { m*         = m*
    ; m*-reached = λ X∈W → m*-reached (W⊆V X∈W)
    }
    where open IsPartiallyAsynchronouslySafe V-safe

  
-}


{-
module _ {a₁ a₂ ℓ₁ ℓ₂ n} {𝕊₁ : IndexedSetoid (Fin n) a₁ ℓ₁} {𝕊₂ : IndexedSetoid (Fin n) a₂ ℓ₂}
         {P₁ : Parallelisation 𝕊₁} {P₂ : Parallelisation 𝕊₂}
         (P₁↭P₂ : Bisimilar P₁ P₂) (P₁-isSafe : IsAsynchronouslySafe P₁) where


  private
  
    module P = Parallelisation P₁
    module Q = Parallelisation P₂

    open Bisimilar P₁↭P₂
    open IsAsynchronouslySafe P₁-isSafe
      renaming (m* to m*₁; m*-reached to m*₁-reached)

    open Schedule


    asyncIter-eq : ∀ s X → ∀ {t} (tAcc : Acc _<_ t) →
                   to (P.asyncIter' s (from X) tAcc) Q.≈ Q.asyncIter' s X tAcc
    asyncIter-eq s X {zero}  _          i = toᵢ-fromᵢ (X i)
    asyncIter-eq s X {suc t} (acc tAcc) i with i ∈? α s (suc t)
    ... | yes _ = Q.≈ᵢ-trans (toᵢ-F _) (F-cong (λ j → asyncIter-eq s X (tAcc (β s (suc t) i j) _) j) i)
    ... | no  _ = asyncIter-eq s X (tAcc _ ≤-refl) i


    m*₂ : Q.S
    m*₂ = to m*₁

    m*₂-reached : ∀ X s → ∃ λ tᶜ → ∀ t → Q.asyncIter s X (tᶜ + t) Q.≈ m*₂
    m*₂-reached X s with m*₁-reached (from X) s
    ... | (tᶜ , converged) = tᶜ , (λ t i → Q.≈ᵢ-trans
      (Q.≈-sym (asyncIter-eq s X (<-wellFounded (tᶜ + t))) i)
      (toᵢ-cong (converged t i)))


  bisimulation : IsAsynchronouslySafe P₂
  bisimulation = record
    { m*         = m*₂
    ; m*-reached = m*₂-reached
    }
-}
