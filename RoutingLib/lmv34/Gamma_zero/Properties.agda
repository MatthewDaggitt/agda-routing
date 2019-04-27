open import Data.Fin using (Fin)
open import Data.Nat using (zero; suc)
open import Algebra.FunctionProperties
import Relation.Binary.EqReasoning as EqReasoning

open import RoutingLib.lmv34.Function using (_^_)
open import RoutingLib.Routing.Algebra using (RawRoutingAlgebra)
open import RoutingLib.Routing as Routing using (AdjacencyMatrix)
import RoutingLib.lmv34.Gamma_zero as Gamma_zero
import RoutingLib.lmv34.Gamma_zero.Algebra as Gamma_zero_Algebra

module RoutingLib.lmv34.Gamma_zero.Properties
  {a b ℓ} (algebra : RawRoutingAlgebra a b ℓ)
  {n} (A : AdjacencyMatrix algebra n)
  where

open Routing algebra n renaming (I to M)
open RawRoutingAlgebra algebra
open Gamma_zero algebra A
open Gamma_zero_Algebra algebra n

------------------------------------
-- Operation properties

⊕ₘ-cong : Congruent₂ _≈ₘ_ _⊕ₘ_
⊕ₘ-cong A=A' B=B' i j = ⊕-cong (A=A' i j) (B=B' i j)

⨁-cong : ∀ {k} → {f g : Fin k → Route} →
         (∀ {i} → f i ≈ g i) → ⨁ f ≈ ⨁ g
⨁-cong {zero} f=g = ≈-refl
⨁-cong {suc k} f=g = ⊕-cong f=g (⨁-cong {k} f=g)

〔〕-cong : ∀ {A X X'} → X ≈ₘ X' → (A 〔 X 〕) ≈ₘ (A 〔 X' 〕)
〔〕-cong {A} X=X' i j = ⨁-cong (λ {k} → ▷-cong (A i k) (X=X' k j))

Γ₀-cong : ∀ {X X'} → X ≈ₘ X' → Γ₀ X ≈ₘ Γ₀ X'
Γ₀-cong X=X' = ⊕ₘ-cong (〔〕-cong X=X') ≈ₘ-refl

------------------------------------
-- Theorems

-- Theorem 1
FixedPoint-Γ₀ : ∀ {k Y} → (Γ₀ ^ suc k) Y ≈ₘ (Γ₀ ^ k) Y →
                let X = (Γ₀ ^ k) Y in
                X ≈ₘ (A 〔 X 〕 ⊕ₘ M)
FixedPoint-Γ₀ {k} {Y} FP = begin
  (Γ₀ ^ k) Y              ≈⟨ ≈ₘ-sym FP ⟩
  (Γ₀ ^ suc k) Y          ≈⟨ ≈ₘ-refl ⟩
  A 〔 (Γ₀ ^ k) Y 〕 ⊕ₘ M ∎
  where open EqReasoning (ℝ𝕄ₛ)
