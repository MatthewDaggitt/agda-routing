open import Data.Fin using (Fin)
open import Data.Nat using (zero; suc)
open import Algebra.Bundles using (Magma)
open import Algebra.Structures using (IsMagma)
open import Algebra.Definitions
open import Relation.Binary using (DecSetoid)
import Relation.Binary.Reasoning.Setoid as EqReasoning
open import Relation.Unary using (Pred)

open import RoutingLib.Algebra.Bundles using (DecMagma)
open import RoutingLib.Algebra.Structures using (IsDecMagma)
open import RoutingLib.Iteration.Synchronous using (_^_; IsFixedPoint)
open import RoutingLib.Routing.Algebra using (RawRoutingAlgebra)
open import RoutingLib.Routing as Routing using (AdjacencyMatrix)
import RoutingLib.lmv34.Synchronous.Gamma_zero as Gamma_zero
import RoutingLib.lmv34.Synchronous.Gamma_zero.Algebra as Gamma_zero_Algebra

module RoutingLib.lmv34.Synchronous.Gamma_zero.Properties
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

⊕ₘ-isMagma : IsMagma _≈ₘ_ _⊕ₘ_
⊕ₘ-isMagma = record
  { isEquivalence = ≈ₘ-isEquivalence
  ; ∙-cong        = ⊕ₘ-cong
  }

⊕ₘ-magma : Magma _ _
⊕ₘ-magma = record
  { isMagma = ⊕ₘ-isMagma
  }

⊕ₘ-isDecMagma : IsDecMagma _≈ₘ_ _⊕ₘ_
⊕ₘ-isDecMagma = record
  { isMagma = ⊕ₘ-isMagma
  ; _≟_     = _≟ₘ_
  }

⊕ₘ-decMagma : DecMagma _ _
⊕ₘ-decMagma = record
  { isDecMagma = ⊕ₘ-isDecMagma
  }

⨁-cong : ∀ {k} → {f g : Fin k → Route} →
         (∀ {i} → f i ≈ g i) → ⨁ f ≈ ⨁ g
⨁-cong {zero} f=g = ≈-refl
⨁-cong {suc k} f=g = ⊕-cong f=g (⨁-cong {k} f=g)

〔〕-cong : ∀ {A X X'} → X ≈ₘ X' → (A 〔 X 〕) ≈ₘ (A 〔 X' 〕)
〔〕-cong {A} X=X' i j = ⨁-cong (λ {k} → ▷-cong (A i k) (X=X' k j))

Γ₀-cong : Congruent₁ _≈ₘ_ Γ₀
Γ₀-cong X=X' = ⊕ₘ-cong (〔〕-cong X=X') ≈ₘ-refl

IsFixedPoint-Γ₀ : Pred RoutingMatrix ℓ
IsFixedPoint-Γ₀ Y = Γ₀ Y ≈ₘ Y

------------------------------------
-- Theorems

-- Theorem 1
FixedPoint-Γ₀ : ∀ {k Y} → (Γ₀ ^ suc k) Y ≈ₘ (Γ₀ ^ k) Y →
                 IsFixedPoint-Γ₀ ((Γ₀ ^ k) Y)
FixedPoint-Γ₀ FP = FP
