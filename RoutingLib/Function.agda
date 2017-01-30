open import Function using (id; _∘_)
open import Data.Nat using (ℕ; zero; suc)

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

module RoutingLib.Function where

  infix 7 _^_

  _^_ : ∀ {a} {A : Set a} → (A → A) → ℕ → (A → A)
  f ^ zero    = id
  f ^ (suc n) = f ∘ (f ^ n)


  ff^≡f^f : ∀ {a} {A : Set a} (f : A → A) n x → f ((f ^ n) x) ≡ (f ^ n) (f x)
  ff^≡f^f f zero x    = refl
  ff^≡f^f f (suc n) x = cong f (ff^≡f^f f n x)
