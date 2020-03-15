open import Algebra
open import RoutingLib.Algebra.Bundles

module RoutingLib.Algebra.Construct.Lexicographic.Magma
  {a b ℓ₁ ℓ₂} (DM₁ : DecMagma a ℓ₁) (M₂ : Magma b ℓ₂)
  where

open import Algebra.Structures
open import Data.Product
open import Data.Product.Relation.Binary.Pointwise.NonDependent
open import Data.Sum
open import Level using (_⊔_)
open import Relation.Binary
open import Relation.Nullary using (yes; no; ¬_)
open import Relation.Nullary.Negation using (contradiction)

open import RoutingLib.Algebra.Construct.Lexicographic as Lex using (Lex)

------------------------------------------------------------------------
-- Prelude

private
  open module Mᵃ = DecMagma DM₁ using ()
    renaming (Carrier to A; _≈_ to _≈ᵃ_; _∙_ to _∙ᵃ_; _≟_ to _≟ᵃ_)

  open module Mᵇ = Magma M₂ using ()
    renaming (Carrier to B; _≈_ to _≈ᵇ_; _∙_ to _∙ᵇ_)

  infix 4 _≈ₓ_
  
  _≈ₓ_ : Rel _ (ℓ₁ ⊔ ℓ₂)
  _≈ₓ_ = Pointwise _≈ᵃ_ _≈ᵇ_

  _≉₁_ : Rel A _
  x ≉₁ y = ¬ (x ≈ᵃ y)

------------------------------------------------------------------------
-- Definition

infix 7 _⊕ₗₑₓ_

_⊕ₗₑₓ_ : Op₂ (A × B)
_⊕ₗₑₓ_ = Lex _≟ᵃ_ _∙ᵃ_ _∙ᵇ_

------------------------------------------------------------------------
-- Algebraic properties

cong : Congruent₂ _≈ₓ_ _⊕ₗₑₓ_
cong = Lex.cong DM₁ M₂

assoc : Associative _≈ᵃ_ _∙ᵃ_ → Associative _≈ᵇ_ _∙ᵇ_ →
        Selective   _≈ᵃ_ _∙ᵃ_ → Commutative _≈ᵃ_ _∙ᵃ_ →
        Associative _≈ₓ_ _⊕ₗₑₓ_
assoc = Lex.assoc DM₁ M₂

comm : Commutative _≈ᵃ_ _∙ᵃ_ → Commutative _≈ᵇ_ _∙ᵇ_ → Commutative _≈ₓ_ _⊕ₗₑₓ_
comm = Lex.comm DM₁ M₂

sel : Selective _≈ᵃ_ _∙ᵃ_ → Selective _≈ᵇ_ _∙ᵇ_ → Selective _≈ₓ_ _⊕ₗₑₓ_
sel = Lex.sel DM₁ M₂

zeroʳ : ∀ {0₁ 0₂} → RightZero _≈ᵃ_ 0₁ _∙ᵃ_ → RightZero _≈ᵇ_ 0₂ _∙ᵇ_ →
        RightZero _≈ₓ_ (0₁ , 0₂) _⊕ₗₑₓ_
zeroʳ = Lex.zeroʳ DM₁ M₂

identityʳ : ∀ {e f} → RightIdentity _≈ᵃ_ e _∙ᵃ_ → RightIdentity _≈ᵇ_ f _∙ᵇ_ →
            RightIdentity _≈ₓ_ (e , f) _⊕ₗₑₓ_
identityʳ = Lex.identityʳ DM₁ M₂

------------------------------------------------------------------------
-- Other properties

Lex-case₁ : ∀ {a b} x y → (a ∙ᵃ b) ≈ᵃ a → (a ∙ᵃ b) ≉₁ b → (a , x) ⊕ₗₑₓ (b , y) ≈ₓ (a , x)
Lex-case₁ = Lex.Lex-case-1 DM₁ M₂

Lex-case₂ : ∀ {a b} x y → (a ∙ᵃ b) ≉₁ a → (a ∙ᵃ b) ≈ᵃ b → (a , x) ⊕ₗₑₓ (b , y) ≈ₓ (b , y)
Lex-case₂ = Lex.Lex-case-2 DM₁ M₂

Lex-case₃ : ∀ {a b} x y → (a ∙ᵃ b) ≈ᵃ a → (a ∙ᵃ b) ≈ᵃ b → (a , x) ⊕ₗₑₓ (b , y) ≈ₓ (a , x ∙ᵇ y)
Lex-case₃ = Lex.Lex-case-3 DM₁ M₂
