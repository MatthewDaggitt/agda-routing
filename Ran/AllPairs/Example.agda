-- imports
open import Data.Nat
  using (ℕ; zero; suc)
open import NatInf
  using (ℕ∞; ∞; N)
open import Data.Fin
  using (Fin) renaming (zero to fzero; suc to fsuc)
open import Schedule
  using (Schedule; 𝕋)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl)
open import Schedule.Synchronous
  using (synchronous-schedule)

module AllPairs.Example where

  row₁ : Fin 5 → ℕ∞
  row₁ fzero                             = N 0
  row₁ (fsuc fzero)                      = N 3
  row₁ (fsuc (fsuc fzero))               = N 8
  row₁ (fsuc (fsuc (fsuc fzero)))        = ∞
  row₁ (fsuc (fsuc (fsuc (fsuc fzero)))) = N 4
  row₁ (fsuc (fsuc (fsuc (fsuc (fsuc ())))))
  row₂ : Fin 5 → ℕ∞
  row₂ fzero                             = ∞
  row₂ (fsuc fzero)                      = N 0
  row₂ (fsuc (fsuc fzero))               = ∞
  row₂ (fsuc (fsuc (fsuc fzero)))        = N 1
  row₂ (fsuc (fsuc (fsuc (fsuc fzero)))) = N 7
  row₂ (fsuc (fsuc (fsuc (fsuc (fsuc ())))))
  row₃ : Fin 5 → ℕ∞
  row₃ fzero                             = ∞
  row₃ (fsuc fzero)                      = N 4
  row₃ (fsuc (fsuc fzero))               = N 0
  row₃ (fsuc (fsuc (fsuc fzero)))        = ∞
  row₃ (fsuc (fsuc (fsuc (fsuc fzero)))) = ∞
  row₃ (fsuc (fsuc (fsuc (fsuc (fsuc ())))))
  row₄ : Fin 5 → ℕ∞
  row₄ fzero                             = N 2
  row₄ (fsuc fzero)                      = ∞
  row₄ (fsuc (fsuc fzero))               = N 5
  row₄ (fsuc (fsuc (fsuc fzero)))        = N 0
  row₄ (fsuc (fsuc (fsuc (fsuc fzero)))) = ∞
  row₄ (fsuc (fsuc (fsuc (fsuc (fsuc ())))))
  row₅ : Fin 5 → ℕ∞
  row₅ fzero                             = ∞
  row₅ (fsuc fzero)                      = ∞
  row₅ (fsuc (fsuc fzero))               = ∞
  row₅ (fsuc (fsuc (fsuc fzero)))        = N 6
  row₅ (fsuc (fsuc (fsuc (fsuc fzero)))) = N 0
  row₅ (fsuc (fsuc (fsuc (fsuc (fsuc ())))))

  grid : Fin 5 → Fin 5 → ℕ∞
  grid fzero = row₁
  grid (fsuc fzero) = row₂
  grid (fsuc (fsuc fzero)) = row₃
  grid (fsuc (fsuc (fsuc fzero))) = row₄
  grid (fsuc (fsuc (fsuc (fsuc fzero)))) = row₅
  grid (fsuc (fsuc (fsuc (fsuc (fsuc ())))))

  s : Schedule 5
  s = synchronous-schedule 5

  Cᵢ,ᵢ : ∀ i → grid i i ≡ N 0
  Cᵢ,ᵢ fzero = refl
  Cᵢ,ᵢ (fsuc fzero) = refl
  Cᵢ,ᵢ (fsuc (fsuc fzero)) = refl
  Cᵢ,ᵢ (fsuc (fsuc (fsuc fzero))) = refl
  Cᵢ,ᵢ (fsuc (fsuc (fsuc (fsuc fzero)))) = refl
  Cᵢ,ᵢ (fsuc (fsuc (fsuc (fsuc (fsuc ())))))

  open import AllPairs.Convergence s grid Cᵢ,ᵢ
    using (convergence; result)

  t : 𝕋
  t = convergence

  r : Fin 5 → Fin 5 → ℕ∞
  r = result
