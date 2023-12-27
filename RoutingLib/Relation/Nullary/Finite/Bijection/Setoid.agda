open import Relation.Binary hiding (Decidable)

module RoutingLib.Relation.Nullary.Finite.Bijection.Setoid where

open import Data.Fin hiding (_+_; suc)
open import Data.Fin.Properties using (any?; eq?)
open import Data.List.Membership.Setoid
open import Data.Product
open import Data.Nat using (ℕ)
open import Data.Sum using (_⊎_)
open import Function
open import Level
open import Relation.Nullary
open import Relation.Unary using (Pred; Decidable)
import Relation.Nullary.Decidable as Dec
open import Relation.Binary.PropositionalEquality using (_≡_; setoid)
open import Data.Product.Relation.Binary.Pointwise.NonDependent using (_×ₛ_)
open import Data.Sum.Relation.Binary.Pointwise using (_⊎ₛ_)

open Setoid using (Carrier)

private
  variable
    a b ℓ ℓ₁ ℓ₂ p : Level
    
  𝔽 : ℕ → Setoid 0ℓ 0ℓ
  𝔽 n = setoid (Fin n)

------------------------------------------------------------------------
-- Definitions

record Finite (S : Setoid a ℓ) : Set (a ⊔ suc ℓ) where
  field
    n         : ℕ
    bijection : Bijection S (𝔽 n) 

  open Bijection bijection public
  open Setoid S renaming (Carrier to A)
  
  f⁻¹ : Fin n → A
  f⁻¹ i = proj₁ (strictlySurjective i)

  f∘f⁻¹ : ∀ x → to (f⁻¹ x) ≡ x
  f∘f⁻¹ i = proj₂ (strictlySurjective i)

  f⁻¹∘f : ∀ x → f⁻¹ (to x) ≈ x
  f⁻¹∘f x = injective (f∘f⁻¹ (to x))


Countable : (S : Setoid a ℓ) → Set _
Countable S = Injection S (setoid ℕ)

CountablyInfinite : (S : Setoid a ℓ) → Set _
CountablyInfinite S = Bijection (setoid ℕ) S
