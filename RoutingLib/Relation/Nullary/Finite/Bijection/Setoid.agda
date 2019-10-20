open import Relation.Binary hiding (Decidable)

module RoutingLib.Relation.Nullary.Finite.Bijection.Setoid where

open import Data.Fin hiding (_+_)
open import Data.Fin.Properties using (any?; eq?)
open import Data.List.Membership.Setoid
open import Data.Product
open import Data.Nat
open import Data.Sum using (_⊎_)
open import Function
open import Level
open import Relation.Nullary
open import Relation.Unary using (Pred; Decidable)
import Relation.Nullary.Decidable as Dec
open import Relation.Binary.PropositionalEquality using (setoid)
open import Data.Product.Relation.Pointwise.NonDependent using (_×ₛ_)
open import Data.Sum.Relation.Pointwise using (_⊎ₛ_)

open import RoutingLib.Function

open Setoid using (Carrier)

private
  variable
    a b ℓ ℓ₁ ℓ₂ p : Level
    
  𝔽 : ℕ → Setoid 0ℓ 0ℓ
  𝔽 n = setoid (Fin n)

Finite : (S : Setoid a ℓ) → Set _
Finite S = ∃ λ n → Bijection (𝔽 n) S

Countable : (S : Setoid a ℓ) → Set _
Countable S = Injection (setoid ℕ) S

CountablyInfinite : (S : Setoid a ℓ) → Set _
CountablyInfinite S = Bijection (setoid ℕ) S

map′ : ∀ {S : Setoid a ℓ₁} {T : Setoid b ℓ₂} → Equivalence S T → Dec (Carrier S) → Dec (Carrier T)
map′ eq (yes p) = yes (f p)
  where open Equivalence eq
map′ eq (no ¬p) = no (¬p ∘ g)
  where open Equivalence eq

{-
Finiteᴸ : Set _
Finiteᴸ = ∃ λ as → ∀ a → a ∈ as
-}

{-
module _ (S : Setoid a ℓ) where

  open Setoid S renaming (Carrier to A)
  
  module _ {P : Pred A p} (resp : P Respects _≈_) where

    finite⇒∃? : (P? : Decidable P) → Finite S → Dec (∃ P)
    finite⇒∃? P? (n , f-bij) = Dec.map′ (map f id) (map _ (resp (proj₂ (surjective _)))) (any? (P? ∘ f))
      where open Bijection f-bij

module _ {S : Setoid a ℓ₁} {T : Setoid b ℓ₂} where

  _×ᶠ_ : Finite S → Finite T → Finite (S ×ₛ T)
  (m , Sₙ) ×ᶠ (n , Tₙ) = m * n , {!!}

  _⊎ᶠ_ : Finite S → Finite T → Finite (S ⊎ₛ T)
  (m , Sₙ) ⊎ᶠ (n , Tₙ) = m + n , {!!}
-}
