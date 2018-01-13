open import Data.Nat using (ℕ; zero; suc; s≤s; _<_; _+_; _⊓_)
open import Data.Nat.Properties using (m⊓n≤n)
open import Data.Fin hiding (_<_; _+_)
open import Data.Fin.Properties

open import Function using (_∘_)

module RoutingLib.Data.Fin where

  _+↑_ : ∀ {n} → Fin n → Fin n → Fin n
  _+↑_ {zero}  ()
  _+↑_ {suc n} i j = fromℕ≤ (s≤s (m⊓n≤n (toℕ i + toℕ j) n))
