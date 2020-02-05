open import Data.Product using (_,_; proj₂; proj₁)
open import Data.Sum using (inj₁; inj₂)
open import Function using (_∘_)
open import Relation.Binary
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Negation using (contradiction)

open import RoutingLib.Relation.Binary

module RoutingLib.Relation.Binary.Construct.NonStrictToStrict
  {a ℓ₁ ℓ₂} {A : Set a} (_≈_ : Rel A ℓ₁) (_≤_ : Rel A ℓ₂)
  where

  open import Relation.Binary.Construct.NonStrictToStrict _≈_ _≤_

  <-min : Symmetric _≈_ → ∀ {⊥} → Minimum _≤_ ⊥ → StrictMinimum _≈_ _<_ ⊥
  <-min sym min {x} x≉⊥ = min x , x≉⊥ ∘ sym

  <-max : ∀ {⊤} → Maximum _≤_ ⊤ → StrictMaximum _≈_ _<_ ⊤
  <-max max {x} x≉⊤ = max x , x≉⊤
