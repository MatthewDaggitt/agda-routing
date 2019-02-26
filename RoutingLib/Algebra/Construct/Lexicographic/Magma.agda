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

open import RoutingLib.Algebra.Construct.Lexicographic
  as Lex using (Lex)
open import RoutingLib.Function
open import RoutingLib.Algebra.FunctionProperties

------------------------------------------------------------------------
-- Prelude

private
  open module Mᵃ = DecMagma DM₁ using ()
    renaming (Carrier to A; _≈_ to _≈ᵃ_; _∙_ to _∙ᵃ_)

  open module Mᵇ = Magma DM₂ using ()
    renaming (Carrier to B; _≈_ to _≈ᵇ_; _∙_ to _∙ᵇ_)

  _≈ₗₑₓ_ : Rel (A × B) (ℓ₁ ⊔ ℓ₂)
  _≈ₗₑₓ_ = Pointwise _≈ᵃ_ _≈ᵇ_
    
------------------------------------------------------------------------
-- Definition

_⊕ₗₑₓ_ : Op₂ (A × B)
_⊕ₗₑₓ_ = Lex Mᵃ._≟_ _∙ᵃ_ _∙ᵇ_

------------------------------------------------------------------------
-- Algebraic properties

assoc : Associative _≈ᵃ_ _∙ᵃ_ → Associative _≈ᵇ_ _∙ᵇ_ → Associative _≈ₗₑₓ_ _⊕ₗₑₓ_
assoc = Lex.assoc Mᵃ._≟_ _≈ᵇ_ _∙ᵃ_ _∙ᵇ_ Mᵃ.refl Mᵇ.refl Mᵃ.trans

comm : Commutative _≈ᵃ_ _∙ᵃ_ → Commutative _≈ᵇ_ _∙ᵇ_ → Commutative _≈ₗₑₓ_ _⊕ₗₑₓ_
comm = Lex.comm Mᵃ._≟_ _≈ᵇ_ _∙ᵃ_ _∙ᵇ_ Mᵃ.refl Mᵇ.refl Mᵃ.trans

sel : Selective _≈ᵃ_ _∙ᵃ_ → Selective _≈ᵇ_ _∙ᵇ_ → Selective _≈ₗₑₓ_ _⊕ₗₑₓ_
sel = Lex.sel Mᵃ._≟_ _≈ᵇ_ _∙ᵃ_ _∙ᵇ_ Mᵃ.refl Mᵇ.refl

zeroʳ : ∀ {0₁ 0₂} → RightZero _≈ᵃ_ 0₁ _∙ᵃ_ → RightZero _≈ᵇ_ 0₂ _∙ᵇ_ →
        RightZero _≈ₗₑₓ_ (0₁ , 0₂) _⊕ₗₑₓ_
zeroʳ = Lex.zeroʳ Mᵃ._≟_ _≈ᵇ_ _∙ᵃ_ _∙ᵇ_ Mᵃ.refl Mᵇ.refl

cong : Congruent₂ _≈ₗₑₓ_ _⊕ₗₑₓ_
cong = Lex.cong Mᵃ._≟_ _≈ᵇ_ _∙ᵃ_ _∙ᵇ_ Mᵃ.sym Mᵃ.trans Mᵃ.∙-cong Mᵇ.∙-cong

opLex-proj₁ : ∀ x y → proj₁ (x ⊕ₗₑₓ y) ≈ᵃ ((proj₁ x) ∙ᵃ (proj₁ y))
opLex-proj₁ = Lex.opLex-proj₁ Mᵃ._≟_ _≈ᵇ_ _∙ᵃ_ _∙ᵇ_ Mᵃ.refl Mᵃ.sym
