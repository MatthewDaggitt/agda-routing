
open import Algebra using (Semiring)

module RoutingLib.db716.Results.MatrixPowerSums {c ℓ} (S : Semiring c ℓ) where

open import Data.Nat using (ℕ; suc)
open import Data.Fin using (Fin; _≟_)
open import Data.List using (List; []; _∷_; _++_; foldr; map)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)

open import RoutingLib.Data.Matrix using (SquareMatrix)

open import RoutingLib.Data.Matrix.Algebra.Semiring S
open import RoutingLib.Algebra.Properties.Semiring.Sum S
open import RoutingLib.Data.Matrix

open import RoutingLib.db716.Data.Path.UncertifiedFinite
open import RoutingLib.db716.Data.Path.UncertifiedFinite.Weights S
open import RoutingLib.db716.Results.MatrixPowers S using (mat-pows-find-best-paths; folds-lemma2)

open Semiring S

private pow : ∀ {n} → SquareMatrix Carrier n → ℕ → SquareMatrix Carrier n
pow {n} = pow'
  where open import RoutingLib.db716.Algebra.Semiring (⊕-⊗-semiring n) using () renaming (pow to pow')

private powSum : ∀ {n} → SquareMatrix Carrier n → ℕ → SquareMatrix Carrier n
powSum {n} = powSum'
  where open import RoutingLib.db716.Algebra.Semiring (⊕-⊗-semiring n) using () renaming (powSum to powSum')

mat-pow-sums-find-best-paths : ∀ n k (i j : Vertex n) (M : SquareMatrix Carrier n) → powSum M k i j ≈ best-path-weight M (all-≤k-length-paths-from-to n k i j)
mat-pow-sums-find-best-paths n ℕ.zero i j M with i ≟ j
... | yes i≡j = sym (+-identityʳ 1#)
... | no i≢j = refl
mat-pow-sums-find-best-paths n (suc k) i j M = begin
  powSum M (suc k) i j
    ≡⟨⟩
  powSum M k i j + pow M (suc k) i j
    ≈⟨ +-cong (mat-pow-sums-find-best-paths n k i j M) (mat-pows-find-best-paths n (suc k) i j M) ⟩
  best-path-weight M (all-≤k-length-paths-from-to n k i j) + best-path-weight M (all-k-length-paths-from-to n (suc k) i j)
    ≈⟨ folds-lemma2 n (weight M) (all-≤k-length-paths-from-to n k i j) (all-k-length-paths-from-to n (suc k) i j) ⟩
  best-path-weight M (all-≤k-length-paths-from-to n k i j ++ all-k-length-paths-from-to n (suc k) i j)
    ≡⟨⟩
  best-path-weight M (all-≤k-length-paths-from-to n (suc k) i j) ∎
  where open import Relation.Binary.Reasoning.Setoid setoid

