
module RoutingLib.Data.FiniteSet where

open import Data.Fin
open import Data.Fin.Patterns
open import Data.Nat
open import Data.Product hiding (map)
open import Data.Vec.Functional hiding (map; last)
open import Data.Unit using (⊤)
open import Function
open import Level using (Level)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Unary using (Pred)
open import Relation.Binary using (Setoid)

open import RoutingLib.Data.Vec.Functional hiding (⟦_⟧)
open import RoutingLib.Relation.Nullary.Finite.Bijection.Setoid using (Finite)

private
  variable
    a b : Level
    A : Set a
    B : Set b

--------------------------------------------------------------------------------
-- FiniteSet
--------------------------------------------------------------------------------

record FiniteSet (A : Set a) : Set a where
  constructor ⟦_∣_⟧
  field
    n            : ℕ
    x            : Vector A (suc n)

∣_∣ : FiniteSet A → ℕ
∣ ⟦ n ∣ _ ⟧ ∣ = suc n

content : (X : FiniteSet A) → Vector A ∣ X ∣
content ⟦ _ ∣ x ⟧ = x

⟦_⟧ : A → FiniteSet A
⟦ x ⟧ = ⟦ 0 ∣ const x ⟧

⟦_⟧₂ : A × A → FiniteSet A
⟦ x , y ⟧₂ = ⟦ 1 ∣ (λ {0F → x; 1F → y}) ⟧

⟦_⟧∪_ : A → FiniteSet A → FiniteSet A
⟦ y ⟧∪ ⟦ n ∣ X ⟧ = ⟦ suc n ∣ y ∷ X ⟧

_∪⟦_⟧ : FiniteSet A → A → FiniteSet A
⟦ n ∣ X ⟧ ∪⟦ y ⟧ = ⟦ suc n ∣ X ∷ʳ y ⟧

first : FiniteSet A → A
first ⟦ _ ∣ x ⟧ = x 0F

last : FiniteSet A → A
last ⟦ n ∣ x ⟧ = x (fromℕ n)

iᵗʰ : (X : FiniteSet A) → Fin ∣ X ∣ → A
iᵗʰ ⟦ _ ∣ x ⟧ i = x i 

map : (A → B) → FiniteSet A → FiniteSet B
map f ⟦ n ∣ x ⟧ = ⟦ n ∣ f ∘ x ⟧ 
