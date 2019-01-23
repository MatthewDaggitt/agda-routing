open import RoutingLib.Routing.Algebra
open import Agda.Primitive
open import Relation.Binary.PropositionalEquality.Core
open import Relation.Binary using (IsDecEquivalence)
open import Relation.Binary using (Decidable)
open import Relation.Nullary
open import Function using (_$_; const)
open import RoutingLib.Data.NatInf using (ℕ∞; ∞; N; _⊓_; _≟_)
open import Data.Nat using (zero; suc)

module RoutingLib.lmv34.ShortestPathsAlgebra where

▷-cong : (f : (ℕ∞ → ℕ∞)) → ∀ {x y} → x ≡ y → (f x) ≡ (f y)
▷-cong f refl = refl

⊓-mono : ∀ {a b c d} → a ≡ c → b ≡ d → a ⊓ b ≡ c ⊓ d
⊓-mono refl refl = refl

ShortestPathAlgebra : RawRoutingAlgebra _ _ _
ShortestPathAlgebra = record
  { Route = ℕ∞
  ; Step = λ i j → ℕ∞ → ℕ∞
  ; _≈_ = _≡_
  ; _⊕_ = _⊓_
  ; _▷_ = _$_
  ; 0# = (N zero)
  ; ∞ = ∞
  ; f∞ = λ i j n → ∞
  ; ≈-isDecEquivalence = record
    { isEquivalence = isEquivalence
    ; _≟_ = _≟_ }
  ; ⊕-cong = ⊓-mono
  ; ▷-cong = ▷-cong
  ; f∞-reject = λ i j x → refl
  }

