open import Relation.Binary

module RoutingLib.Relation.Binary.Construct.TransitiveClosure
  {a r} {A : Set a} {R : Rel A r} where

open import Data.Fin
open import Data.Nat
open import Data.Product
open import Relation.Binary.Construct.Closure.Transitive
open import Relation.Nullary using (¬_)

open import RoutingLib.Relation.Nullary using (Finite)

R⁺ : Rel A _
R⁺ = Plus′ R

steps : ∀ {x y} → R⁺ x y → ℕ
steps [ x∼y ]      = 2
steps (x∼y ∷ x∼*y) = suc (steps x∼*y)

index : ∀ {x y} (R⁺xy : R⁺ x y) → Fin (steps R⁺xy) → A
index {x} {y} [ x∼y ]    0F      = x
index {x} {y} (x∼y ∷ xy) 0F      = x
index {x} {y} [ x∼y ]    1F      = y
index {x} {y} (x∼y ∷ xy) (suc i) = index xy i

trans : Transitive R⁺
trans [ x∼y ]     Ryz = x∼y ∷ Ryz
trans (w∼x ∷ Rxy) Ryz = w∼x ∷ trans Rxy Ryz

postulate R⁺? : Finite A → Decidable R → Decidable R⁺

module _ {ℓ} {_≈_ : Rel A ℓ} where

  R⁺-respˡ-≈ : R Respectsˡ _≈_ → R⁺ Respectsˡ _≈_
  R⁺-respˡ-≈ resp x≈y [ x∼y ]     = [ resp x≈y x∼y ]
  R⁺-respˡ-≈ resp x≈y (x∼y ∷ Rxz) = resp x≈y x∼y ∷ Rxz

  R⁺-respʳ-≈ : R Respectsʳ _≈_ → R⁺ Respectsʳ _≈_
  R⁺-respʳ-≈ resp x≈y [ x∼y ]     = [ resp x≈y x∼y ]
  R⁺-respʳ-≈ resp x≈y (x∼y ∷ Rzx) = x∼y ∷ R⁺-respʳ-≈ resp x≈y Rzx
  
  R⁺-resp-≈ : R Respects₂ _≈_ → R⁺ Respects₂ _≈_
  R⁺-resp-≈ (respʳ , respˡ) = R⁺-respʳ-≈ respʳ , R⁺-respˡ-≈ respˡ
