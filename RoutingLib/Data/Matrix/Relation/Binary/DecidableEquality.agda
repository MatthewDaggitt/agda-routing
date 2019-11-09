open import Relation.Binary using (DecSetoid)

module RoutingLib.Data.Matrix.Relation.Binary.DecidableEquality
  {a ℓ} (DS : DecSetoid a ℓ) where

open import Data.Nat using (ℕ)
open import Data.Product using (∃₂; _,_)
open import Data.Fin.Dec using (all?;  ¬∀⟶∃¬)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Negation using (contradiction)

open import RoutingLib.Data.Matrix
open import RoutingLib.Data.Matrix.Relation.Binary.Pointwise
  using () renaming (decSetoid to pointwiseDecSetoid)

open DecSetoid DS using (_≈_; _≟_) renaming (setoid to S; Carrier to A)
open import RoutingLib.Data.Matrix.Relation.Binary.Equality S public
open import RoutingLib.Data.Vec.Functional.Relation.Binary.DecidableEquality DS

Dec𝕄ₛ : ℕ → ℕ → DecSetoid a ℓ
Dec𝕄ₛ m n = pointwiseDecSetoid DS m n

module _ {m n : ℕ} where
  open DecSetoid (Dec𝕄ₛ m n) public using ()
    renaming
    ( _≟_ to _≟ₘ_)

≉ₘ-witness : ∀ {m n} {X Y : Matrix A m n} →
             X ≉ₘ Y → ∃₂ λ i j → ¬ (X i j ≈ Y i j)
≉ₘ-witness {m} {n} {X} {Y} X≉Y with all? (λ i → all? (λ j → X i j ≟ Y i j))
... | yes all  = contradiction all X≉Y
... | no  ¬all with ¬∀⟶∃¬ m _ (λ i → all? (λ j → X i j ≟ Y i j)) ¬all
...   | (i , Xᵢ≉Yᵢ) = (i , ≉ₜ-witness Xᵢ≉Yᵢ)
