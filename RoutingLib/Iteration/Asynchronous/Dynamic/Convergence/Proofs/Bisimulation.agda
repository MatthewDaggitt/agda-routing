open import Data.Nat using (zero; suc; _<_; _+_)
open import Data.Nat.Properties using (≤-refl)
open import Data.Fin.Subset using (Subset)
open import Data.Fin.Subset.Properties using (_∈?_)
open import Data.Product using (∃; _,_)
open import Induction.WellFounded using (Acc; acc)
open import Induction.Nat using (<-wellFounded)
import Relation.Binary.EqReasoning as EqReasoning
open import Relation.Nullary using (yes; no)

open import RoutingLib.Relation.Unary.Indexed

open import RoutingLib.Iteration.Asynchronous.Dynamic
open import RoutingLib.Iteration.Asynchronous.Dynamic.Schedule
open import RoutingLib.Iteration.Asynchronous.Dynamic.Schedule.Pseudoperiod

module RoutingLib.Iteration.Asynchronous.Dynamic.Convergence.Proofs.Bisimulation
  {a₁ a₂ ℓ₁ ℓ₂ n}
  {P∥ : AsyncIterable a₁ ℓ₁ n}
  {Q∥ : AsyncIterable a₂ ℓ₂ n}
  (P∥-convergent : Convergent P∥)
  (P∥∼Q∥ : Bisimilar P∥ Q∥)
  where

  private
  
    module P = AsyncIterable P∥
    module Q = AsyncIterable Q∥

    open Bisimilar P∥∼Q∥
    open ConvergentOver P∥-convergent
      renaming (x* to y*; x*-fixed to y*-fixed; x*-reached to y*-reached)

    open Schedule

    asyncIter-eq : ∀ s x₀ → ∀ {t} (tAcc : Acc _<_ t) →
                   to (asyncIter' P∥ s (from x₀) tAcc) Q.≈ asyncIter' Q∥ s x₀ tAcc
    asyncIter-eq s x₀ {zero} _ i with i ∈? ρ s 0
    ... | no  _ = toᵢ-⊥
    ... | yes _ = toᵢ-fromᵢ (x₀ i)
    asyncIter-eq s x₀ {suc t} (acc tAcc) i with i ∈? ρ s (suc t) | i ∈? ρ s t | i ∈? α s (suc t)
    ... | no  _      | _     | _     = toᵢ-⊥
    ... | yes _      | no  _ | _     = toᵢ-fromᵢ (x₀ i)
    ... | yes _      | yes _ | no  _ = asyncIter-eq s x₀ (tAcc _ ≤-refl) i
    ... | yes i∈ρ₁₊ₜ | yes _ | yes _ = Q.≈ᵢ-trans (toᵢ-F _) (Q.F-cong (η s (suc t)) (ρ s (suc t)) (λ {j} _ → asyncIter-eq s x₀ (tAcc (β s (suc t) i j) _) j) i∈ρ₁₊ₜ)
    x* : Epoch → Subset n → Q.S
    x* e p = to (y* e p)

    x*-fixed : ∀ e p → Q.F e p (x* e p) Q.≈ x* e p
    x*-fixed e p = begin
      Q.F e p (x* e p)      ≈⟨ Q.≈-sym (to-F (y* e p)) ⟩
      to (P.F e p (y* e p)) ≈⟨ to-cong (y*-fixed e p) ⟩
      to (y* e p)           ≡⟨⟩
      x* e p                ∎
      where open EqReasoning Q.≈-setoid
      
    x*-reached : ∀ {x₀} → x₀ ∈ U Q.Sᵢ → (𝓢 : Schedule n) → {s : 𝕋} →
                 ∃ λ k → ∀ {m e : 𝕋} → 
                 IsMultiPseudoperiodic 𝓢 k [ s , m ] →
                 IsSubEpoch 𝓢 [ m , e ] →
                 asyncIter Q∥ 𝓢 x₀ e Q.≈ x* (η 𝓢 s) (ρ 𝓢 s)
    x*-reached {x₀} x₀∈U s with y*-reached x₀∈U s
    ... | (k , converges) = k , (λ {m} {e} ppₖ η[m,e] i → Q.≈ᵢ-trans
      (Q.≈-sym (asyncIter-eq s x₀ (<-wellFounded e)) i)
      (toᵢ-cong (converges ppₖ η[m,e] i)))
    

  bisimulation : Convergent Q∥ 
  bisimulation = record
    { x*         = x*
    ; x*-fixed   = x*-fixed
    ; x*-reached = x*-reached
    }
