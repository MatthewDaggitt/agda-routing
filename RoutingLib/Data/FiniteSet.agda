
module RoutingLib.Data.FiniteSet where

open import Data.Fin
open import Data.Fin.Patterns
open import Data.Nat
open import Data.Product
open import Data.Vec.Functional
open import Function
open import Level using (Level)

open import RoutingLib.Data.Vec.Functional hiding (⟦_⟧)

private
  variable
    a : Level
    A : Set a

--------------------------------------------------------------------------------
-- FiniteSet
--------------------------------------------------------------------------------

record FiniteSet (A : Set a) : Set a where
  constructor ⟦_∣_⟧
  field
    m : ℕ
    x : Vector A (suc m)

∣_∣ : FiniteSet A → ℕ
∣ ⟦ n ∣ _ ⟧ ∣ = suc n

⟦_⟧ : A → FiniteSet A
⟦ x ⟧ = ⟦ 0 ∣ const x ⟧

⟦_⟧₂ : A × A → FiniteSet A
⟦ x , y ⟧₂ = ⟦ 1 ∣ (λ {0F → x; 1F → y}) ⟧

⟦_⟧∪_ : A → FiniteSet A → FiniteSet A
⟦ y ⟧∪ ⟦ n ∣ X ⟧ = ⟦ suc n ∣ [ y ]+ X ⟧

_∪⟦_⟧ : FiniteSet A → A → FiniteSet A
⟦ n ∣ X ⟧ ∪⟦ y ⟧ = ⟦ suc n ∣ X +[ y ]  ⟧

first : FiniteSet A → A
first ⟦ _ ∣ x ⟧ = x 0F

last : FiniteSet A → A
last ⟦ n ∣ x ⟧ = x (fromℕ n)

iᵗʰ : (X : FiniteSet A) → Fin ∣ X ∣ → A
iᵗʰ ⟦ _ ∣ x ⟧ i = x i 
