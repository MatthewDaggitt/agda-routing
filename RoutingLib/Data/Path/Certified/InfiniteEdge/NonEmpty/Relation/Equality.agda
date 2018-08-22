open import Data.Fin using (Fin)
open import Data.Nat using (ℕ) renaming (_≟_ to _≟ℕ_)
open import Data.Product using (∃₂; _,_; _×_)
open import Level using () renaming (zero to ℓ₀)
open import Relation.Binary
open import Relation.Binary.Product.Pointwise using (_×-≟_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import Relation.Nullary using (¬_; yes; no)

open import RoutingLib.Data.Path.EdgePath.NonEmpty

module RoutingLib.Data.Path.EdgePath.NonEmpty.Relation.Equality where

----------------------------------------------------------------------------
-- Relations

infix 4 _≈ₚ_ _≉ₚ_

data _≈ₚ_ : Rel Pathⁿᵗ ℓ₀ where
  []  : [] ≈ₚ []
  _∷_ : ∀ {e f p q w x y z} → e ≡ f → p ≈ₚ q → e ∷ p ∣ w ∣ x ≈ₚ f ∷ q ∣ y ∣ z

_≉ₚ_ : Rel Pathⁿᵗ ℓ₀
p ≉ₚ q = ¬ (p ≈ₚ q)

----------------------------------------------------------------------------
-- Properties

private

  _≟ₑ_ : Decidable {A = ℕ × ℕ} _≡_
  _≟ₑ_ = _≟ℕ_ ×-≟ _≟ℕ_

abstract

  p≉i∷p : ∀ {e p} {e⇿p e∉p} → ¬ (p ≈ₚ e ∷ p ∣ e⇿p ∣ e∉p)
  p≉i∷p {p = []}            ()
  p≉i∷p {p = _ ∷ _ ∣ _ ∣ _} (_ ∷ p≈ₚi∷p) = p≉i∷p p≈ₚi∷p

  -- Injectivity properties

  module _ {i j k l p q w x y z} where

    ∷ˡ-injective₁ : (i , j) ∷ p ∣ w ∣ x ≈ₚ (k , l) ∷ q ∣ y ∣ z → i ≡ k
    ∷ˡ-injective₁ (refl ∷ _) = refl

    ∷ˡ-injective₂ : (i , j) ∷ p ∣ w ∣ x ≈ₚ (k , l) ∷ q ∣ y ∣ z → j ≡ l
    ∷ˡ-injective₂ (refl ∷ _) = refl

    ∷ʳ-injective : (i , j) ∷ p ∣ w ∣ x ≈ₚ (k , l) ∷ q ∣ y ∣ z → p ≈ₚ q
    ∷ʳ-injective (_ ∷ p≈q) = p≈q

  -- Algebraic properties
  ≈ₚ-refl : Reflexive _≈ₚ_
  ≈ₚ-refl {[]}            = []
  ≈ₚ-refl {_ ∷ _ ∣ _ ∣ _} = refl ∷ ≈ₚ-refl

  ≈ₚ-reflexive : _≡_ ⇒ _≈ₚ_
  ≈ₚ-reflexive refl = ≈ₚ-refl

  ≈ₚ-sym : Symmetric _≈ₚ_
  ≈ₚ-sym []           = []
  ≈ₚ-sym (refl ∷ p≈ₚq) = refl ∷ (≈ₚ-sym p≈ₚq)

  ≈ₚ-trans : Transitive _≈ₚ_
  ≈ₚ-trans []            []           = []
  ≈ₚ-trans (refl ∷ p≈ₚq)  (refl ∷ q≈ₚr) = refl ∷ (≈ₚ-trans p≈ₚq q≈ₚr)
  
  _≟ₚ_ : Decidable _≈ₚ_
  []              ≟ₚ []              = yes []
  []              ≟ₚ (k ∷ q ∣ _ ∣ _) = no λ()
  (i ∷ p ∣ _ ∣ _) ≟ₚ []              = no λ()
  (i ∷ p ∣ _ ∣ _) ≟ₚ (k ∷ q ∣ _ ∣ _) with i ≟ₑ k | p ≟ₚ q
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
ℙₛ = record { isEquivalence = ≈ₚ-isEquivalence }

ℙₛ? : DecSetoid ℓ₀ ℓ₀
ℙₛ? = record { isDecEquivalence = ≈ₚ-isDecEquivalence }
