open import Algebra
open import RoutingLib.Algebra

module RoutingLib.Algebra.Construct.Lexicographic.Magma
  {a b ℓ₁ ℓ₂} (DM₁ : DecMagma a ℓ₁) (DM₂ : Magma b ℓ₂)
  where

open import Algebra.FunctionProperties
open import Data.Product
open import Data.Product.Relation.Pointwise.NonDependent
open import Data.Sum
open import Level using (_⊔_)
open import Relation.Binary
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Negation using (contradiction)

open import RoutingLib.Algebra.Construct.Lexicographic as Lex using (Lex)
open import RoutingLib.Function
open import RoutingLib.Algebra.FunctionProperties

------------------------------------------------------------------------
-- Prelude

private
  open module Mᵃ = DecMagma DM₁ using ()
    renaming (Carrier to A; _≈_ to _≈ᵃ_; _∙_ to _∙ᵃ_; _≟_ to _≟ᵃ_; isEquivalence to ≈ᵃ-isEquivalence; ∙-cong to ∙ᵃ-cong)

  open module Mᵇ = Magma DM₂ using ()
    renaming (Carrier to B; _≈_ to _≈ᵇ_; _∙_ to _∙ᵇ_; isEquivalence to ≈ᵇ-isEquivalence; ∙-cong to ∙ᵇ-cong)

  _≈ₗₑₓ_ : Rel (A × B) (ℓ₁ ⊔ ℓ₂)
  _≈ₗₑₓ_ = Pointwise _≈ᵃ_ _≈ᵇ_

  ≈ᵃ-isDecEquivalence : IsDecEquivalence _≈ᵃ_
  ≈ᵃ-isDecEquivalence = record { isEquivalence = ≈ᵃ-isEquivalence ; _≟_ = _≟ᵃ_ }

------------------------------------------------------------------------
-- Definition

_⊕ₗₑₓ_ : Op₂ (A × B)
_⊕ₗₑₓ_ = Lex Mᵃ._≟_ _∙ᵃ_ _∙ᵇ_

------------------------------------------------------------------------
-- Algebraic properties

assoc : Associative _≈ᵃ_ _∙ᵃ_ → Associative _≈ᵇ_ _∙ᵇ_ → Selective _≈ᵃ_ _∙ᵃ_ → Commutative _≈ᵃ_ _∙ᵃ_ → Associative _≈ₗₑₓ_ _⊕ₗₑₓ_
assoc = Lex.assoc ≈ᵃ-isDecEquivalence ≈ᵇ-isEquivalence _∙ᵃ_ _∙ᵇ_ ∙ᵃ-cong ∙ᵇ-cong

comm : Commutative _≈ᵃ_ _∙ᵃ_ → Commutative _≈ᵇ_ _∙ᵇ_ → Commutative _≈ₗₑₓ_ _⊕ₗₑₓ_
comm = Lex.comm ≈ᵃ-isDecEquivalence ≈ᵇ-isEquivalence  _∙ᵃ_ _∙ᵇ_ ∙ᵃ-cong ∙ᵇ-cong

sel : Selective _≈ᵃ_ _∙ᵃ_ → Selective _≈ᵇ_ _∙ᵇ_ → Selective _≈ₗₑₓ_ _⊕ₗₑₓ_
sel = Lex.sel ≈ᵃ-isDecEquivalence ≈ᵇ-isEquivalence  _∙ᵃ_ _∙ᵇ_ ∙ᵃ-cong ∙ᵇ-cong

zeroʳ : ∀ {0₁ 0₂} → RightZero _≈ᵃ_ 0₁ _∙ᵃ_ → RightZero _≈ᵇ_ 0₂ _∙ᵇ_ → RightZero _≈ₗₑₓ_ (0₁ , 0₂) _⊕ₗₑₓ_
zeroʳ = Lex.zeroʳ ≈ᵃ-isDecEquivalence ≈ᵇ-isEquivalence  _∙ᵃ_ _∙ᵇ_ ∙ᵃ-cong ∙ᵇ-cong

identityʳ : ∀ {e f} → RightIdentity _≈ᵃ_ e _∙ᵃ_ → RightIdentity _≈ᵇ_ f _∙ᵇ_ → RightIdentity _≈ₗₑₓ_ (e , f) _⊕ₗₑₓ_
identityʳ = Lex.identityʳ ≈ᵃ-isDecEquivalence ≈ᵇ-isEquivalence  _∙ᵃ_ _∙ᵇ_ ∙ᵃ-cong ∙ᵇ-cong

cong : Congruent₂ _≈ₗₑₓ_ _⊕ₗₑₓ_
cong = Lex.cong ≈ᵃ-isDecEquivalence ≈ᵇ-isEquivalence  _∙ᵃ_ _∙ᵇ_ ∙ᵃ-cong ∙ᵇ-cong

-- ------------------------------------------------------------------------
-- -- Other properties

-- opLex-proj₁ : ∀ x y → proj₁ (x ⊕ₗₑₓ y) ≈ᵃ ((proj₁ x) ∙ᵃ (proj₁ y))
-- opLex-proj₁ = ? -- Lex.opLex-proj₁ Mᵃ._≟_ _≈ᵇ_ _∙ᵃ_ _∙ᵇ_ Mᵃ.refl Mᵃ.sym
