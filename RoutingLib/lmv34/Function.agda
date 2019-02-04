open import Data.Nat using (ℕ; zero; suc)
open import Function using (id; _∘_)

module RoutingLib.lmv34.Function where

infix 20 _^_
_^_ : ∀ {a} {A : Set a} → (A → A) → ℕ → A → A
f ^ zero = id
f ^ (suc n) = f ∘ (f ^ n)
