open import Relation.Binary

module RoutingLib.Relation.Binary.Construct.Closure.Transitive where

open import Data.Fin.Subset
open import Data.Fin.Subset.Properties
open import Data.Nat.Induction
open import Data.Nat using (ℕ; zero; suc; z≤n; s≤s; _<_; _≤_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; n≤1+n)
open import Data.Product as Prod
open import Level using (Level; _⊔_)
open import Function using (_∘_)
open import Relation.Binary.Construct.Closure.Transitive
open import Relation.Nullary using (¬_; Dec; yes; no)
import Relation.Nullary.Decidable as Dec
open import Relation.Nullary.Product
open import Relation.Nary using ()
open import Relation.Unary as U using (Pred)

open import RoutingLib.Function
open import RoutingLib.Relation.Nullary
open import RoutingLib.Data.Fin.Subset
open import RoutingLib.Data.Fin.Subset.Properties

open Setoid using (Carrier)

private
  variable
    a r ℓ : Level

trans : ∀ {A : Set a} {R : Rel A r} → Transitive (Plus′ R)
trans [ x∼y ]     Ryz = x∼y ∷ Ryz
trans (w∼x ∷ Rxy) Ryz = w∼x ∷ trans Rxy Ryz

module _ {ℓ r} {A : Set a} {_≈_ : Rel A r} {R : Rel A ℓ} where

  R⁺-respˡ-≈ : R Respectsˡ _≈_ → (Plus′ R) Respectsˡ _≈_
  R⁺-respˡ-≈ resp x≈y [ x∼y ]     = [ resp x≈y x∼y ]
  R⁺-respˡ-≈ resp x≈y (x∼y ∷ Rxz) = resp x≈y x∼y ∷ Rxz

  R⁺-respʳ-≈ : R Respectsʳ _≈_ → (Plus′ R) Respectsʳ _≈_
  R⁺-respʳ-≈ resp x≈y [ x∼y ]     = [ resp x≈y x∼y ]
  R⁺-respʳ-≈ resp x≈y (x∼y ∷ Rzx) = x∼y ∷ R⁺-respʳ-≈ resp x≈y Rzx
  
  R⁺-resp-≈ : R Respects₂ _≈_ → (Plus′ R) Respects₂ _≈_
  R⁺-resp-≈ (respʳ , respˡ) = R⁺-respʳ-≈ respʳ , R⁺-respˡ-≈ respˡ
