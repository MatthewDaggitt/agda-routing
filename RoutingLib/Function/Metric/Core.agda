

module RoutingLib.Function.Metric.Core where

open import Algebra.FunctionProperties
open import Data.Product
open import Level using (Level; _⊔_)
open import Relation.Binary hiding (Symmetric)
open import Relation.Binary.PropositionalEquality
import Relation.Binary.Construct.NonStrictToStrict as NonStrictToStrict
open import Relation.Nullary using (¬_)
open import Relation.Unary

private
  variable
    a i ℓ ℓ₁ ℓ₂ : Level
    A : Set a
    I : Set i
    
------------------------------------------------------------------------
-- Definition

Distance : Set a → Set i → Set _
Distance A I = A → A → I

------------------------------------------------------------------------
-- Properties

-- Basic

Indiscernability : Rel A ℓ₁ → Rel I ℓ₂ → Distance A I → I → Set _
Indiscernability _≈ₐ_ _≈ᵢ_ d 0# = ∀ {x y} → d x y ≈ᵢ 0# → x ≈ₐ y

PositiveDefinite : Rel A ℓ₁ → Rel I ℓ₂ →  Distance A I → I → Set _
PositiveDefinite _≈ₐ_ _≈ᵢ_ d 0# = ∀ {x y} → x ≈ₐ y → d x y ≈ᵢ 0#

Symmetric : Rel I ℓ → Distance A I → Set _
Symmetric _≈_ d = ∀ x y → d x y ≈ d y x

TriangleIneq : Rel I ℓ → Op₂ I → Distance A I → _
TriangleIneq _≤_ _∙_ d = ∀ x y z → d x z ≤ (d x y ∙ d y z)

-- Contractions

Contracting : Rel I ℓ → (A → A) → Distance A I → Set _
Contracting _≤_ f d = ∀ x y → d (f x) (f y) ≤ d x y

ContractingOnOrbits : Rel I ℓ → (A → A) → Distance A I → Set _
ContractingOnOrbits _≤_ f d = ∀ x → d (f x) (f (f x)) ≤ d x (f x)

StrictlyContracting : Rel A ℓ₁ → Rel I ℓ₂ → (A → A) → Distance A I → Set _
StrictlyContracting _≈_ _<_ f d = ∀ {x y} → ¬ (y ≈ x) → d (f x) (f y) < d x y

StrictlyContractingOnOrbits : Rel A ℓ₁ → Rel I ℓ₂ → (A → A) → Distance A I → Set _
StrictlyContractingOnOrbits _≈_ _<_ f d = ∀ {x} → ¬ (f x ≈ x) → d (f x) (f (f x)) < d x (f x)

StrictlyContractingOnFixedPoints : Rel A ℓ₁ → Rel I ℓ₂ → (A → A) → Distance A I → Set _
StrictlyContractingOnFixedPoints _≈_ _<_ f d = ∀ {x x*} → f x* ≈ x* → ¬ (x ≈ x*) → d x* (f x) < d x* x

-- Others

Bounded : Rel I ℓ → Distance A I → Set _
Bounded _≤_ d = ∃ λ n → ∀ x y → d x y ≤ n

TranslationInvariant : Rel I ℓ₂ → Op₂ A → Distance A I → Set _
TranslationInvariant _≈_ _∙_ d = ∀ {x y a} → d (x ∙ a) (y ∙ a) ≈ d x y
