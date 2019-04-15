
module RoutingLib.Function.Metric.Nat.Core where

open import Algebra.FunctionProperties using (Op₂)
open import Data.Nat
open import Level using (Level)
open import Relation.Binary hiding (Symmetric)
open import Relation.Binary.PropositionalEquality using (_≡_)

import RoutingLib.Function.Metric.Core as Base

private
  variable
    a ℓ : Level
    A   : Set a
    _≈_ : Rel A ℓ
    d   : A → A → ℕ

------------------------------------------------------------------------
-- Definition

Distance : Set a → Set a
Distance A = Base.Distance A ℕ

------------------------------------------------------------------------
-- Properties

-- Basic

Symmetric : Distance A → Set _
Symmetric = Base.Symmetric _≡_

TriangleInequality : Distance A → Set _
TriangleInequality = Base.TriangleIneq _≤_ _+_

MaxTriangleInequality : Distance A → Set _
MaxTriangleInequality = Base.TriangleIneq _≤_ _⊔_

-- Contractions

Contracting : (A → A) → Distance A → Set _
Contracting = Base.Contracting _≤_

ContractingOnOrbits : (A → A) → Distance A → Set _
ContractingOnOrbits = Base.ContractingOnOrbits _≤_

StrictlyContracting : Rel A ℓ → (A → A) → Distance A → Set _
StrictlyContracting _≈_ = Base.StrictlyContracting _≈_ _<_

StrictlyContractingOnOrbits : Rel A ℓ → (A → A) → Distance A → Set _
StrictlyContractingOnOrbits _≈_ = Base.StrictlyContractingOnOrbits _≈_ _<_

StrictlyContractingOnFixedPoints : Rel A ℓ → (A → A) → Distance A → Set _
StrictlyContractingOnFixedPoints _≈_ = Base.StrictlyContractingOnFixedPoints _≈_ _<_

-- Other

Bounded : Distance A → Set _
Bounded = Base.Bounded _≤_

TranslationInvariant : Op₂ A → Distance A → Set _
TranslationInvariant = Base.TranslationInvariant _≡_
