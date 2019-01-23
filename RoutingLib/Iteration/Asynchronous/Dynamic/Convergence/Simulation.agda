open import Data.Nat using (zero; suc; _<_; _+_)
open import Data.Nat.Properties using (≤-refl)
open import Data.Fin.Subset using (Subset)
open import Data.Fin.Subset.Properties using (_∈?_)
open import Data.Product using (∃; _,_)
open import Data.Unit using (tt)
open import Induction.WellFounded using (Acc; acc)
open import Induction.Nat using (<-wellFounded)
import Relation.Binary.EqReasoning as EqReasoning
open import Relation.Nullary using (yes; no)
open import Relation.Unary

open import RoutingLib.Relation.Unary.Indexed using (IPred; _∈ᵢ_; Uᵢ)

open import RoutingLib.Iteration.Asynchronous.Dynamic
open import RoutingLib.Iteration.Asynchronous.Dynamic.Schedule
open import RoutingLib.Iteration.Asynchronous.Dynamic.Schedule.Pseudoperiod

module RoutingLib.Iteration.Asynchronous.Dynamic.Convergence.Simulation
  {a₁ a₂ ℓ₁ ℓ₂ n}
  {I∥ : AsyncIterable a₁ ℓ₁ n}
  {J∥ : AsyncIterable a₂ ℓ₂ n}
  (I∥⇉J∥ : Simulates I∥ J∥)
  where

  open Simulates I∥⇉J∥

  private
    module I = AsyncIterable I∥
    module J = AsyncIterable J∥

  module _ {ℓ₃ ℓ₄ ℓ₅} {B₀ : IPred I.Sᵢ ℓ₃} {C₀ : IPred J.Sᵢ ℓ₄}
           (C₀⊆B₀ : ∀ {x} → x ∈ᵢ C₀ → from x ∈ᵢ B₀)
           {Q  : Pred (Subset n) ℓ₅}
           (I-convergent : PartiallyConvergent I∥ B₀ Q)
           where

    open Schedule
    open PartiallyConvergent I-convergent
      renaming
      ( x*         to y*
      ; x*-fixed   to y*-fixed
      ; x*-reached to y*-reached
      )

    asyncIter-eq : ∀ s x₀ → ∀ {t} (tAcc : Acc _<_ t) →
                   to (asyncIter' I∥ s (from x₀) tAcc) J.≈ asyncIter' J∥ s x₀ tAcc
    asyncIter-eq s x₀ {zero} _ i with i ∈? ρ s 0
    ... | no  _ = toᵢ-⊥
    ... | yes _ = toᵢ-fromᵢ (x₀ i)
    asyncIter-eq s x₀ {suc t} (acc tAcc) i with i ∈? ρ s (suc t) | i ∈? ρ s t | i ∈? α s (suc t)
    ... | no  _      | _     | _     = toᵢ-⊥
    ... | yes _      | no  _ | _     = toᵢ-fromᵢ (x₀ i)
    ... | yes _      | yes _ | no  _ = asyncIter-eq s x₀ (tAcc _ ≤-refl) i
    ... | yes i∈ρ₁₊ₜ | yes _ | yes _ = J.≈ᵢ-trans (toᵢ-F _) (J.F-cong (η s (suc t)) (ρ s (suc t)) (λ j → asyncIter-eq s x₀ (tAcc (β s (suc t) i j) _) j) i∈ρ₁₊ₜ)

    x* : Epoch → {p : Subset n} → p ∈ Q → J.S
    x* e {p} p∈Q = to (y* e {p} p∈Q)

    x*-fixed : ∀ e {p} (p∈Q : p ∈ Q) → J.F e p (x* e p∈Q) J.≈ x* e p∈Q
    x*-fixed e {p} p∈Q = begin
      J.F e p (x* e p∈Q)      ≈⟨ J.≈-sym (to-F (y* e p∈Q)) ⟩
      to (I.F e p (y* e p∈Q)) ≈⟨ to-cong (y*-fixed e p∈Q) ⟩
      to (y* e p∈Q)           ≡⟨⟩
      x* e p∈Q                ∎
      where open EqReasoning J.≈-setoid

    x*-reached : ∀ {x₀} → x₀ ∈ᵢ C₀ → {𝓢 : Schedule n} (ρ∈Q : 𝓢 satisfies Q) → {s m e : 𝕋} →
                 IsMultiPseudoperiodic 𝓢 (k* (η 𝓢 s) (ρ∈Q s)) [ s , m ] →
                 IsSubEpoch 𝓢 [ m , e ] →
                 asyncIter J∥ 𝓢 x₀ e J.≈ x* (η 𝓢 s) (ρ∈Q s)
    x*-reached {x₀} x₀∈C₀ {S} ρ∈Q {s} {m} {e} ppₖ η[m,e] i = J.≈ᵢ-trans
      (J.≈-sym (asyncIter-eq S x₀ (<-wellFounded e)) i)
      (toᵢ-cong (y*-reached (C₀⊆B₀ x₀∈C₀) ρ∈Q ppₖ η[m,e] i))

    simulate : PartiallyConvergent J∥ C₀ Q
    simulate = record
      { x*         = x*
      ; k*         = k*
      ; x*-fixed   = x*-fixed
      ; x*-reached = x*-reached
      }
