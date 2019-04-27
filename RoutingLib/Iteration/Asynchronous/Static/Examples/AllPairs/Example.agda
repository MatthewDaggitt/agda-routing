-- imports
open import Data.Nat
  using (ℕ; zero; suc)
open import Data.Fin
  using (Fin) renaming (zero to fzero; suc to fsuc)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl)

open import RoutingLib.Data.NatInf using (ℕ∞; N; ∞)

module RoutingLib.Iteration.Asynchronous.Static.Examples.AllPairs.Example where

  pattern 0# = fzero
  pattern 1# = fsuc fzero
  pattern 2# = fsuc (fsuc fzero)
  pattern 3# = (fsuc (fsuc (fsuc fzero)))
  pattern 4# = (fsuc (fsuc (fsuc (fsuc fzero))))
  
  grid : Fin 5 → Fin 5 → ℕ∞
  grid 0# 0# = N 0
  grid 0# 1# = N 3
  grid 0# 2# = N 8
  grid 0# 3# = ∞
  grid 0# 4# = N 4
  grid 1# 0# = ∞
  grid 1# 1# = N 0
  grid 1# 2# = ∞
  grid 1# 3# = N 1
  grid 1# 4# = N 7
  grid 2# 0# = ∞
  grid 2# 1# = N 4
  grid 2# 2# = N 0
  grid 2# 3# = ∞
  grid 2# 4# = ∞
  grid 3# 0# = N 2
  grid 3# 1# = ∞
  grid 3# 2# = N 5
  grid 3# 3# = N 0
  grid 3# 4# = ∞
  grid 4# 0# = ∞
  grid 4# 1# = ∞
  grid 4# 2# = ∞
  grid 4# 3# = N 6
  grid 4# 4# = N 0

  Cᵢ,ᵢ : ∀ i → grid i i ≡ N 0
  Cᵢ,ᵢ 0# = refl
  Cᵢ,ᵢ 1# = refl
  Cᵢ,ᵢ 2# = refl
  Cᵢ,ᵢ 3# = refl
  Cᵢ,ᵢ 4# = refl
