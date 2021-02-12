open import Relation.Binary using (DecSetoid)
open import Data.Nat using (ℕ)
open import Data.Product using (∃)
open import Data.Fin.Properties using (all?; ¬∀⟶∃¬)
open import Data.Vec.Functional
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Negation using (contradiction)
import Data.Vec.Functional.Relation.Binary.Pointwise.Properties as Pointwise

open import RoutingLib.Data.Vec.Functional.Properties

module RoutingLib.Data.Vec.Functional.Relation.Binary.DecidableEquality
  {a ℓ} (DS : DecSetoid a ℓ) where

open DecSetoid DS using (_≈_; _≟_) renaming (setoid to S; Carrier to A)
open import Data.Vec.Functional.Relation.Binary.Equality.Setoid S public

≋-decSetoid : ℕ → DecSetoid a ℓ
≋-decSetoid n = Pointwise.decSetoid DS n

module _ {n : ℕ} where
  open DecSetoid (≋-decSetoid n) public
    using ()
    renaming (_≟_ to _≟ₜ_)

≉ₜ-witness : ∀ {n} {X Y : Vector A n} → ¬ (X ≋ Y) → ∃ λ i → ¬ (X i ≈ Y i)
≉ₜ-witness {n} {X} {Y} X≉Y with all? (λ i → X i ≟ Y i)
... | yes all  = contradiction all X≉Y
... | no  ¬all = ¬∀⟶∃¬ n (λ i → X i ≈ Y i) (λ i → X i ≟ Y i) ¬all
