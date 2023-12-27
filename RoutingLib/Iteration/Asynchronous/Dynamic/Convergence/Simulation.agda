--------------------------------------------------------------------------------
-- Agda routing library
--
-- This module proofs that if I∥ simulates J∥ then if I∥ converges so does J∥
--------------------------------------------------------------------------------

open import Data.Nat using (zero; suc; _<_; _+_)
open import Data.Nat.Properties using (≤-refl)
open import Data.Nat.Induction using (Acc; acc; <-wellFounded)
open import Data.Fin.Subset using (Subset)
open import Data.Fin.Subset.Properties using (_∈?_)
open import Data.Product using (∃; _×_; _,_)
open import Data.Unit using (tt)
import Relation.Binary.Reasoning.Setoid as EqReasoning
open import Relation.Nullary using (yes; no)
open import Relation.Unary

open import RoutingLib.Relation.Unary.Indexed
open import RoutingLib.Iteration.Asynchronous.Dynamic.Schedule
open import RoutingLib.Iteration.Asynchronous.Dynamic.Schedule.Pseudocycle
open import RoutingLib.Iteration.Asynchronous.Dynamic

module RoutingLib.Iteration.Asynchronous.Dynamic.Convergence.Simulation
  {a₁ a₂ ℓ₁ ℓ₂ ℓ₃ ℓ₄ n}
  {I∥ : AsyncIterable a₁ ℓ₁ n} (let module I = AsyncIterable I∥)
  {J∥ : AsyncIterable a₂ ℓ₂ n} (let module J = AsyncIterable J∥)
  {X₀ : IPred I.Sᵢ ℓ₃} {Y₀ : IPred J.Sᵢ ℓ₄}
  (I∥⇉J∥ : PartiallySimulates I∥ J∥ X₀ Y₀)
  where

open PartiallySimulates I∥⇉J∥

--------------------------------------------------------------------------------
-- Proof

module _ {ℓ₅} {Q  : Pred (Epoch × Subset n) ℓ₅}
         (I-convergent : PartiallyConvergent I∥ X₀ Q)
         where

  open PartiallyConvergent I-convergent
    renaming
    ( localFP   to y*-localFP
    ; reachesFP to y*-reachesFP
    )

  module _ where
    open Schedule

    asyncIter-eq : ∀ s x₀ → ∀ {t} (tAcc : Acc _<_ t) →
                   to (asyncIter' I∥ s (from x₀) tAcc) J.≈ asyncIter' J∥ s x₀ tAcc
    asyncIter-eq s x₀ {zero} _ i with i ∈? ρ s 0
    ... | no  _ = toᵢ-⊥
    ... | yes _ = toᵢ-fromᵢ (x₀ i)
    asyncIter-eq s x₀ {suc t} (acc tAcc) i
      with i ∈? ρ s (suc t) | i ∈? ρ s t | i ∈? α s (suc t)
    ... | no  _      | _     | _     = toᵢ-⊥
    ... | yes _      | no  _ | _     = toᵢ-fromᵢ (x₀ i)
    ... | yes _      | yes _ | no  _ = asyncIter-eq s x₀ (tAcc ≤-refl) i
    ... | yes i∈ρ₁₊ₜ | yes _ | yes _ = J.≈ᵢ-trans (toᵢ-F _)
      (J.F-cong (η s (suc t)) (ρ s (suc t))
        (λ j → asyncIter-eq s x₀ (tAcc {β s (suc t) i j} _) j) i∈ρ₁₊ₜ)

  module _ {e : Epoch} {p : Subset n} .(ep∈Q : (e , p) ∈ Q) where
    open LocalFixedPoint (y*-localFP ep∈Q) 
      renaming
      ( x*         to y*
      ; x*-fixed   to y*-fixed
      )
    
    private
      x* : J.S
      x* = to y*

      x*-fixed : J.F e p x* J.≈ x*
      x*-fixed = begin
        J.F e p x*      ≈⟨ J.≈-sym (to-F y*) ⟩
        to (I.F e p y*) ≈⟨ to-cong y*-fixed ⟩
        to y*           ≡⟨⟩
        x*              ∎
        where open EqReasoning J.≈-setoid

    x*-localFP : LocalFixedPoint J∥ e p
    x*-localFP = record
      { x*       = x*
      ; k*       = k*
      ; x*-fixed = x*-fixed
      }

  x*-reachesFP : ∀ (ψ : Schedule n) (open Schedule ψ) →
                 ∀ {x : J.S} → x ∈ᵢ Y₀ →
                 ∀ {tₛ : 𝕋} (ηρ∈Q : (η tₛ , ρ tₛ) ∈ Q) →
                 (open LocalFixedPoint (x*-localFP ηρ∈Q)) →
                 ∀ {tₘ : 𝕋} → MultiPseudocycle ψ k* [ tₛ , tₘ ] →
                 ∀ {tₑ : 𝕋} → SubEpoch ψ [ tₘ , tₑ ] →
                 asyncIter J∥ ψ x tₑ J.≈ x*
  x*-reachesFP ψ {x} x∈Y₀ {s} ηρ∈Q {m} ppₖ {e} η[m,e] i = J.≈ᵢ-trans
    (J.≈-sym (asyncIter-eq ψ x (<-wellFounded e)) i)
    (toᵢ-cong (y*-reachesFP ψ (from-Y₀ x∈Y₀) ηρ∈Q ppₖ η[m,e] i))

  simulate : PartiallyConvergent J∥ Y₀ Q
  simulate = record
    { localFP   = x*-localFP
    ; reachesFP = x*-reachesFP
    }
