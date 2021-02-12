
module RoutingLib.Relation.Binary.Construct.Closure.Transitive where

open import Data.Product as Prod
open import Level using (Level)
open import Relation.Binary
open import Relation.Binary.Construct.Closure.Transitive

private
  variable
    a r ℓ : Level
    A : Set a
    R : Rel A r
    
refl : Reflexive R → Reflexive (TransClosure R)
refl ref = [ ref ]

trans : Transitive (TransClosure R)
trans [ x∼y ]     Ryz = x∼y ∷ Ryz
trans (w∼x ∷ Rxy) Ryz = w∼x ∷ trans Rxy Ryz

module _ {_≈_ : Rel A r} where

  R⁺-respˡ-≈ : R Respectsˡ _≈_ → (TransClosure R) Respectsˡ _≈_
  R⁺-respˡ-≈ resp x≈y [ x∼y ]     = [ resp x≈y x∼y ]
  R⁺-respˡ-≈ resp x≈y (x∼y ∷ Rxz) = resp x≈y x∼y ∷ Rxz

  R⁺-respʳ-≈ : R Respectsʳ _≈_ → (TransClosure R) Respectsʳ _≈_
  R⁺-respʳ-≈ resp x≈y [ x∼y ]     = [ resp x≈y x∼y ]
  R⁺-respʳ-≈ resp x≈y (x∼y ∷ Rzx) = x∼y ∷ R⁺-respʳ-≈ resp x≈y Rzx
  
  R⁺-resp-≈ : R Respects₂ _≈_ → (TransClosure R) Respects₂ _≈_
  R⁺-resp-≈ (respʳ , respˡ) = R⁺-respʳ-≈ respʳ , R⁺-respˡ-≈ respˡ
