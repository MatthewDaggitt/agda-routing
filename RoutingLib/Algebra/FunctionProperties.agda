
open import Function using (id)
open import Relation.Binary using (Rel; Decidable; _Preserves₂_⟶_⟶_; _Preserves_⟶_)
open import Data.Product using (_×_)
open import Level using (_⊔_)
open import Data.Sum using (_⊎_; [_,_]; inj₁; inj₂)
open import Relation.Nullary using (¬_)

module RoutingLib.Algebra.FunctionProperties {a ℓ} {A : Set a} (_≈_ : Rel A ℓ) where

  open import RoutingLib.Algebra.FunctionProperties.Core public
  open import Algebra.FunctionProperties _≈_ using (Op₁; Op₂; Idempotent; Commutative; Associative)

  ---------------
  -- Operators --
  ---------------

  LeftAbsorptive : Op₂ A → Op₂ A → Set _
  LeftAbsorptive _•_ _◦_ = ∀ a b → (a • (b ◦ a)) ≈ a

  StrictlyLeftAbsorptive : Op₂ A → Op₂ A → Set _
  StrictlyLeftAbsorptive _•_ _◦_ = ∀ a b → ((a • (b ◦ a)) ≈ a) × ¬ (((b ◦ a) • a) ≈ (b ◦ a))

  RightAbsorptive : Op₂ A → Op₂ A → Set _
  RightAbsorptive _•_ _◦_ = ∀ a b → ((b ◦ a) • a) ≈ a

  StrictlyRightAbsorptive : Op₂ A → Op₂ A → Set _
  StrictlyRightAbsorptive _•_ _◦_ = ∀ a b → (((b ◦ a) • a) ≈ a) × ¬ ((a • (b ◦ a)) ≈ (b ◦ a))

  -- Denotes that the operator _•_ is selective (i.e. returns one of its two inputs)
  Selective : Op₂ A → Set _
  Selective _•_ = ∀ a b → (a • b) ≈ a ⊎ (a • b) ≈ b


  Unreachable : A → Op₂ A → Set _
  Unreachable a _•_ = ∀ {b c} → ¬ (b ≈ a × c ≈ a) → ¬ ((b • c) ≈ a)

  
  Congruent₁ : Op₁ A → Set _
  Congruent₁ f = f Preserves _≈_ ⟶ _≈_

  Congruent₂ : Op₂ A → Set _
  Congruent₂ ∙ = ∙ Preserves₂ _≈_ ⟶ _≈_ ⟶ _≈_

  ---------------
  -- Orderings --
  ---------------

  _DecreasingOver_ : ∀ {ℓ₂} → Op₂ A → Rel A ℓ₂ → Set _
  _•_ DecreasingOver _≤_ = ∀ {a b} → (a • b) ≤ a

  _IncreasingOver_ : ∀ {ℓ₂} → Op₂ A → Rel A ℓ₂ → Set _
  _•_ IncreasingOver _≤_ = ∀ {a b} → a ≤ (a • b)

{-

  StrictlyLeftIncreasing : Rel A ℓ → Op₂ A → Set _
  StrictlyLeftIncreasing _≤_ _•_ = ∀ {a b} → a  ≤ (a • b) → ¬ ((a • b) ≤ a)
-}

