open import RoutingLib.Routing.Algebra
open import Agda.Primitive
open import Relation.Binary.PropositionalEquality.Core
open import Relation.Binary using(IsDecEquivalence)
open import Relation.Binary using (Decidable)
open import Relation.Nullary
open import Function using (_∘_)

module RoutingLib.lmv34.ShortestPathsAlgebra where

data ℕ⁺ : Set where
  zero : ℕ⁺
  suc  : ℕ⁺ → ℕ⁺
  ∞    : ℕ⁺
  
infixl 6 _+_

_+_ : ℕ⁺ → ℕ⁺ → ℕ⁺
zero + n = n
(suc m) + zero = suc m
(suc m) + (suc n) = suc (m + (suc n))
(suc m) + ∞ = ∞
∞ + _ = ∞

suc-injective : ∀ {m n} → suc m ≡ suc n → m ≡ n
suc-injective refl = refl

_≟_ : Decidable {A = ℕ⁺} _≡_
zero ≟ zero = yes refl
zero ≟ suc n = no (λ ())
zero ≟ ∞ = no (λ ())
suc m ≟ zero = no (λ ())
suc m ≟ suc n with m ≟ n
... | yes refl = yes refl
... | no m≠n = no (m≠n ∘ suc-injective)
suc m ≟ ∞ = no (λ ())
∞ ≟ zero = no (λ ())
∞ ≟ suc n = no (λ ())
∞ ≟ ∞ = yes refl

⊕-cong : ∀ {x y u v} → x ≡ y → u ≡ v → (x + u) ≡ (y + v)
⊕-cong refl refl = refl

▷-cong : (f : (ℕ⁺ → ℕ⁺)) → ∀ {x y} → x ≡ y → (f x) ≡ (f y)
▷-cong f refl = refl

ShortestPathAlgebra : RawRoutingAlgebra _ _ _ 
ShortestPathAlgebra = record
  { Route = ℕ⁺
  ; Step = λ i j → ℕ⁺ → ℕ⁺
  ; _≈_ = _≡_
  ; _⊕_ = _+_
  ; _▷_ = λ f r → f r
  ; 0# = zero
  ; ∞ = ∞
  ; f∞ = λ i j n → ∞
  ; ≈-isDecEquivalence = record
    { isEquivalence = isEquivalence
    ; _≟_ = _≟_ }
  ; ⊕-cong = ⊕-cong
  ; ▷-cong = ▷-cong
  ; f∞-reject = λ i j x → refl
  }

