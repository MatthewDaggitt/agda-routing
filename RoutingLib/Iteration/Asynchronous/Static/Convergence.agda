-------------------------------------------------------------------------------
-- This module publicly exports various pre-conditions for the
-- convergence of a static asynchronous iteration as well as the
-- associated theorems. The theorems in question are proved as special
-- instances of the theorems for dynamic asynchronous iterations.
-------------------------------------------------------------------------------

module RoutingLib.Iteration.Asynchronous.Static.Convergence where

open import RoutingLib.Data.Fin.Subset using (Full)
open import RoutingLib.Function.Reasoning

open import RoutingLib.Iteration.Asynchronous.Static
import RoutingLib.Iteration.Asynchronous.Dynamic as Dynamic
import RoutingLib.Iteration.Asynchronous.Dynamic.Convergence as Dynamic
import RoutingLib.Iteration.Asynchronous.Static.ToDynamic as ToDynamic

-------------------------------------------------------------------------------
-- Publicly re-export convergence conditions

open import RoutingLib.Iteration.Asynchronous.Static.Convergence.Conditions public

-------------------------------------------------------------------------------
-- Results

ACO⇒converges : ∀ {a ℓ n} {I∥ : AsyncIterable a ℓ n} →
                ∀ {p} → ACO I∥ p →
                Converges I∥
ACO⇒converges {I∥ = I∥} {p} = begin⟨_⟩
  ⇒ ACO I∥ p                                  ∴⟨ staticToDynamicACO ⟩
  ⇒ Dynamic.PartialACO I∙∥ {!B∙₀!} Full p     ∴⟨ Dynamic.ACO⇒convergent-partial ⟩
  ⇒ Dynamic.PartiallyConvergent I∙∥ {!!} Full ∴⟨ (λ prf → dynamicToStaticConvergence {!!} {!!}) ⟩
  ⇒ Converges I∥                              ∎
  where open ToDynamic I∥

AMCO⇒
