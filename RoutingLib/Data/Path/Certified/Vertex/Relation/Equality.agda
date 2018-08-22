open import Data.Nat using (ℕ)
open import Level using () renaming (zero to ℓ₀)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (¬_; yes; no)

open import RoutingLib.Data.Path
open import RoutingLib.Data.Path.NonEmpty using (Pathⁿᵗ)
import RoutingLib.Data.Path.NonEmpty.Relation.Equality as NE

module RoutingLib.Data.Path.Relation.Equality where

----------------------------------------------------------------------------
-- Relations

open NE using ([]; _∷_) public

infix 4 _≈ₚ_ _≉ₚ_

data _≈ₚ_ : Rel Path ℓ₀ where
  invalid : invalid  ≈ₚ invalid
  valid   : ∀ {p q} → p NE.≈ₚ q → valid p ≈ₚ valid q

_≉ₚ_ : Rel Path ℓ₀
xs ≉ₚ ys = ¬ (xs ≈ₚ ys)

p≉i∷p : ∀ {e} {p : Pathⁿᵗ} {e⇿p e∉p} → ¬ (valid p ≈ₚ valid (e ∷ p ∣ e⇿p ∣ e∉p))
p≉i∷p (valid v) = NE.p≉i∷p v

----------------------------------------------------------------------------
-- Properties

abstract

  valid-injective : ∀ {p q} → valid p ≈ₚ valid q → p NE.≈ₚ q
  valid-injective (valid p≈q) = p≈q

  ≈ₚ-refl : Reflexive _≈ₚ_
  ≈ₚ-refl {invalid} = invalid
  ≈ₚ-refl {valid p} = valid NE.≈ₚ-refl

  ≈ₚ-reflexive : _≡_ ⇒ _≈ₚ_
  ≈ₚ-reflexive refl = ≈ₚ-refl

  ≈ₚ-sym : Symmetric _≈ₚ_
  ≈ₚ-sym invalid     = invalid
  ≈ₚ-sym (valid p≈ₚq) = valid (NE.≈ₚ-sym p≈ₚq)

  ≈ₚ-trans : Transitive _≈ₚ_
  ≈ₚ-trans invalid     invalid     = invalid
  ≈ₚ-trans (valid p≈ₚq) (valid q≈ₚr) = valid (NE.≈ₚ-trans p≈ₚq q≈ₚr)

  _≟ₚ_ : Decidable _≈ₚ_
  invalid ≟ₚ invalid = yes invalid
  invalid ≟ₚ valid q = no λ()
  valid p ≟ₚ invalid  = no λ()
  valid p ≟ₚ valid q with p NE.≟ₚ q
  ... | no  p≉q = no (λ{(valid p≈q) → p≉q p≈q})
  ... | yes p≈q = yes (valid p≈q)

  ≈ₚ-isEquivalence : IsEquivalence _≈ₚ_
  ≈ₚ-isEquivalence = record
    { refl  = ≈ₚ-refl
    ; sym   = ≈ₚ-sym
    ; trans = ≈ₚ-trans
    }

  ≈ₚ-isDecEquivalence : IsDecEquivalence _≈ₚ_
  ≈ₚ-isDecEquivalence = record
    { isEquivalence = ≈ₚ-isEquivalence
    ; _≟_           = _≟ₚ_
    }

ℙₛ : Setoid ℓ₀ ℓ₀
ℙₛ = record
  { Carrier       = Path
  ; _≈_           = _≈ₚ_
  ; isEquivalence = ≈ₚ-isEquivalence
  }

ℙₛ? : DecSetoid ℓ₀ ℓ₀
ℙₛ? = record
  { Carrier          = Path
  ; _≈_              = _≈ₚ_
  ; isDecEquivalence = ≈ₚ-isDecEquivalence
  }
