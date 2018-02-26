open import Data.Fin using (Fin)
open import Data.Fin.Properties using () renaming (_≟_ to _≟𝔽_)
open import Data.Nat using (ℕ)
open import Data.Product using (_,_; _×_)
open import Level using () renaming (zero to ℓ₀)
open import Relation.Binary
open import Relation.Binary.Product.Pointwise using (_×-≟_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (¬_; yes; no)

open import RoutingLib.Data.SimplePath.NonEmpty

module RoutingLib.Data.SimplePath.NonEmpty.Relation.Equality where

  module _ {n : ℕ} where
  
    ----------------------------------------------------------------------------
    -- Relations
  
    infix 4 _≈ₚ_ _≉ₚ_

    data _≈ₚ_ : Rel (SimplePathⁿᵗ n) ℓ₀ where
      []  : [] ≈ₚ []
      _∷_ : ∀ {e f p q w x y z} → e ≡ f → p ≈ₚ q → e ∷ p ∣ w ∣ x ≈ₚ f ∷ q ∣ y ∣ z

    _≉ₚ_ : Rel (SimplePathⁿᵗ n) ℓ₀
    p ≉ₚ q = ¬ (p ≈ₚ q)


    ----------------------------------------------------------------------------
    -- Properties
  
    private
  
      _≟𝔼_ : Decidable {A = Fin n × Fin n} _≡_
      _≟𝔼_ = _≟𝔽_ ×-≟ _≟𝔽_
    
    abstract

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
      (i ∷ p ∣ _ ∣ _) ≟ₚ (k ∷ q ∣ _ ∣ _) with i ≟𝔼 k | p ≟ₚ q
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

  ℙₛ : ℕ → Setoid ℓ₀ ℓ₀
  ℙₛ n = record 
    { Carrier       = SimplePathⁿᵗ n 
    ; _≈_           = _≈ₚ_ 
    ; isEquivalence = ≈ₚ-isEquivalence 
    }

  ℙₛ? : ℕ → DecSetoid ℓ₀ ℓ₀
  ℙₛ? n = record
    { Carrier          = SimplePathⁿᵗ n 
    ; _≈_              = _≈ₚ_ 
    ; isDecEquivalence = ≈ₚ-isDecEquivalence 
    }
