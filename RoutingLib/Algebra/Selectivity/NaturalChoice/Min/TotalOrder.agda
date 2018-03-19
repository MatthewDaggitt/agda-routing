open import Relation.Binary using (TotalOrder)
open import Algebra.FunctionProperties
open import Algebra.Structures
open import Relation.Binary.Lattice using (Minimum; Maximum)

import RoutingLib.Algebra.Selectivity.NaturalChoice.Min as Min

module RoutingLib.Algebra.Selectivity.NaturalChoice.Min.TotalOrder
  {a ℓ₁ ℓ₂} (TO : TotalOrder a ℓ₁ ℓ₂) where

  open TotalOrder TO renaming (Carrier to A)
  
  infix 7 _⊓_
  
  _⊓_ : Op₂ A
  _⊓_ = Min.min total
  
  ------------------------------------------------------------------------------
  -- Algebraic properties

  ⊓-sel : Selective _≈_ _⊓_
  ⊓-sel = Min.sel total _≈_ Eq.refl
  
  ⊓-cong : Congruent₂ _≈_ _⊓_
  ⊓-cong = Min.cong total Eq.sym antisym ≤-resp-≈

  ⊓-comm : Commutative _≈_ _⊓_
  ⊓-comm = Min.comm total Eq.refl antisym

  ⊓-assoc : Associative _≈_ _⊓_
  ⊓-assoc = Min.assoc total Eq.refl trans antisym

  ⊓-identityˡ : ∀ {⊥} → Maximum _≤_ ⊥ → LeftIdentity _≈_ ⊥ _⊓_
  ⊓-identityˡ = Min.identityˡ total Eq.refl antisym

  ⊓-identityʳ : ∀ {⊥} → Maximum _≤_ ⊥ → RightIdentity _≈_ ⊥ _⊓_
  ⊓-identityʳ = Min.identityʳ total Eq.refl antisym

  ⊓-identity : ∀ {⊥} → Maximum _≤_ ⊥ → Identity _≈_ ⊥ _⊓_
  ⊓-identity = Min.identity total Eq.refl antisym

  ⊓-zeroˡ : ∀ {⊥} → Minimum _≤_ ⊥ → LeftZero _≈_ ⊥ _⊓_
  ⊓-zeroˡ = Min.zeroˡ total Eq.refl antisym

  ⊓-zeroʳ : ∀ {⊥} → Minimum _≤_ ⊥ → RightZero _≈_ ⊥ _⊓_
  ⊓-zeroʳ = Min.zeroʳ total Eq.refl antisym

  ⊓-zero : ∀ {⊥} → Minimum _≤_ ⊥ → Zero _≈_ ⊥ _⊓_
  ⊓-zero = Min.zero total Eq.refl antisym

  ⊓-isSemigroup : IsSemigroup _≈_ _⊓_
  ⊓-isSemigroup = Min.isSemigroup total isPartialOrder

  ⊓-isMonoid : ∀ {⊥} → Maximum _≤_ ⊥ → IsMonoid _≈_ _⊓_ ⊥
  ⊓-isMonoid = Min.isMonoid total isPartialOrder

  ----------------------------------------------------------------------------
  -- Other properties

  x⊓y≈y⇒y≤x : ∀ {x y} → (x ⊓ y) ≈ y → y ≤ x
  x⊓y≈y⇒y≤x = Min.min[x,y]≈y⇒y≤x total reflexive Eq.sym
  
  x⊓y≈x⇒x≤y : ∀ {x y} → (x ⊓ y) ≈ x → x ≤ y
  x⊓y≈x⇒x≤y = Min.min[x,y]≈x⇒x≤y total reflexive Eq.sym
