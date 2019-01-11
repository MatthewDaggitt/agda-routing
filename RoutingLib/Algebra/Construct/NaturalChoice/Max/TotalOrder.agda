open import Relation.Binary using (TotalOrder)
open import Algebra.FunctionProperties
open import Algebra.Structures
open import Relation.Binary.Lattice using (Minimum; Maximum)

import RoutingLib.Algebra.Construct.NaturalChoice.Max as Max

module RoutingLib.Algebra.Construct.NaturalChoice.Max.TotalOrder
  {a ℓ₁ ℓ₂} (TO : TotalOrder a ℓ₁ ℓ₂) where

  open TotalOrder TO renaming (Carrier to A)

  infix 7 _⊔_

  _⊔_ : Op₂ A
  _⊔_ = Max.max total

  ------------------------------------------------------------------------------
  -- Algebraic properties

  ⊔-sel : Selective _≈_ _⊔_
  ⊔-sel = Max.sel total _≈_ Eq.refl

  ⊔-cong : Congruent₂ _≈_ _⊔_
  ⊔-cong = Max.cong total Eq.sym antisym ≤-resp-≈

  ⊔-comm : Commutative _≈_ _⊔_
  ⊔-comm = Max.comm total Eq.refl antisym

  ⊔-assoc : Associative _≈_ _⊔_
  ⊔-assoc = Max.assoc total Eq.refl trans antisym

  ⊔-identityˡ : ∀ {⊥} → Minimum _≤_ ⊥ → LeftIdentity _≈_ ⊥ _⊔_
  ⊔-identityˡ = Max.identityˡ total Eq.refl antisym

  ⊔-identityʳ : ∀ {⊥} → Minimum _≤_ ⊥ → RightIdentity _≈_ ⊥ _⊔_
  ⊔-identityʳ = Max.identityʳ total Eq.refl antisym

  ⊔-identity : ∀ {⊥} → Minimum _≤_ ⊥ → Identity _≈_ ⊥ _⊔_
  ⊔-identity = Max.identity total Eq.refl antisym

  ⊔-zeroˡ : ∀ {⊥} → Maximum _≤_ ⊥ → LeftZero _≈_ ⊥ _⊔_
  ⊔-zeroˡ = Max.zeroˡ total Eq.refl antisym

  ⊔-zeroʳ : ∀ {⊥} → Maximum _≤_ ⊥ → RightZero _≈_ ⊥ _⊔_
  ⊔-zeroʳ = Max.zeroʳ total Eq.refl antisym

  ⊔-zero : ∀ {⊥} → Maximum _≤_ ⊥ → Zero _≈_ ⊥ _⊔_
  ⊔-zero = Max.zero total Eq.refl antisym

  ⊔-isSemigroup : IsSemigroup _≈_ _⊔_
  ⊔-isSemigroup = Max.isSemigroup total isPartialOrder

  ⊔-isMonoid : ∀ {⊥} → Minimum _≤_ ⊥ → IsMonoid _≈_ _⊔_ ⊥
  ⊔-isMonoid = Max.isMonoid total isPartialOrder

  ----------------------------------------------------------------------------
  -- Other properties

  x⊔y≈y⇒x≤y : ∀ {x y} → (x ⊔ y) ≈ y → x ≤ y
  x⊔y≈y⇒x≤y = Max.max[x,y]≈y⇒x≤y total reflexive Eq.sym

  x⊔y≈x⇒y≤x : ∀ {x y} → (x ⊔ y) ≈ x → y ≤ x
  x⊔y≈x⇒y≤x = Max.max[x,y]≈x⇒y≤x total reflexive Eq.sym
