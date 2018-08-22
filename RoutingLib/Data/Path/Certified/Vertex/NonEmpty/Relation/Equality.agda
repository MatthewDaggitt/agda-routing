open import Data.Fin using (Fin)
open import Data.Nat using (ℕ) renaming (_≟_ to _≟ℕ_)
open import Data.Product using (∃; ∃₂; _,_; _×_)
open import Level using () renaming (zero to ℓ₀)
open import Relation.Binary
open import Relation.Binary.Product.Pointwise using (_×-≟_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import Relation.Nullary using (¬_; yes; no)

open import RoutingLib.Data.VertexPath.NonEmpty

module RoutingLib.Data.VertexPath.NonEmpty.Relation.Equality where

----------------------------------------------------------------------------
-- Relations

infix 4 _≈ₚ_ _≉ₚ_

data _≈ₚ_ : Rel Pathⁿᵗ ℓ₀ where
  [_] : ∀ {i j} → i ≡ j → [ i ] ≈ₚ [ j ]
  _∷_ : ∀ {e f p q y z} → e ≡ f → p ≈ₚ q → e ∷ p ∣ y ≈ₚ f ∷ q ∣ z

_≉ₚ_ : Rel Pathⁿᵗ ℓ₀
p ≉ₚ q = ¬ (p ≈ₚ q)

----------------------------------------------------------------------------
-- Properties

abstract

  p≉i∷p : ∀ {e} {p : Pathⁿᵗ} {e∉p} → ¬ (p ≈ₚ e ∷ p ∣ e∉p)
  p≉i∷p {p = [ _ ]}            ()
  p≉i∷p {p = _ ∷ _ ∣ _} (_ ∷ p≈ₚi∷p) = p≉i∷p p≈ₚi∷p

  -- Injectivity properties

  module _ {i j p q x y} where

    ∷ˡ-injective : i ∷ p ∣ x ≈ₚ j ∷ q ∣ y → i ≡ j
    ∷ˡ-injective (refl ∷ _) = refl

    ∷ʳ-injective : i ∷ p ∣ x ≈ₚ j ∷ q ∣ y → p ≈ₚ q
    ∷ʳ-injective (_ ∷ p≈q) = p≈q

  -- Algebraic properties
  ≈ₚ-refl : Reflexive _≈ₚ_
  ≈ₚ-refl {[ _ ]}     = [ refl ]
  ≈ₚ-refl {_ ∷ _ ∣ _} = refl ∷ ≈ₚ-refl

  ≈ₚ-reflexive : _≡_ ⇒ _≈ₚ_
  ≈ₚ-reflexive refl = ≈ₚ-refl

  ≈ₚ-sym : Symmetric _≈ₚ_
  ≈ₚ-sym [ refl ]      = [ refl ]
  ≈ₚ-sym (refl ∷ p≈ₚq) = refl ∷ (≈ₚ-sym p≈ₚq)

  ≈ₚ-trans : Transitive _≈ₚ_
  ≈ₚ-trans [ refl ]       [ refl ]       = [ refl ]
  ≈ₚ-trans (refl ∷ p≈ₚq)  (refl ∷ q≈ₚr) = refl ∷ (≈ₚ-trans p≈ₚq q≈ₚr)
  
  _≟ₚ_ : Decidable _≈ₚ_
  [ i ]       ≟ₚ [ j ]        with i ≟ℕ j
  ... | yes i≡j = yes [ i≡j ]
  ... | no  i≢j = no (λ{ [ i≡j ] → i≢j i≡j })
  [ _ ]       ≟ₚ (k ∷ q ∣ _ ) = no λ()
  (i ∷ p ∣ _) ≟ₚ [ _ ]        = no λ()
  (i ∷ p ∣ _) ≟ₚ (k ∷ q ∣ _) with i ≟ℕ k | p ≟ₚ q
  ... | no  i≢k | _       = no (λ{(i≡k ∷ _) → i≢k i≡k})
  ... | _       | no  p≢q = no (λ{(_ ∷ p≡q) → p≢q p≡q})
  ... | yes i≡k | yes p≡q = yes (i≡k ∷ p≡q)

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
  { Carrier       = Pathⁿᵗ
  ; _≈_           = _≈ₚ_
  ; isEquivalence = ≈ₚ-isEquivalence
  }

ℙₛ? : DecSetoid ℓ₀ ℓ₀
ℙₛ? = record
  { Carrier          = Pathⁿᵗ
  ; _≈_              = _≈ₚ_
  ; isDecEquivalence = ≈ₚ-isDecEquivalence
  }
