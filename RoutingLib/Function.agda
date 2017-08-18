open import Function using (id; _∘_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (∃; _×_)

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

module RoutingLib.Function where

  infix 7 _^ˡ_ _^ʳ_

  
  _^ˡ_ : ∀ {a} {A : Set a} → (A → A) → ℕ → (A → A)
  f ^ˡ zero    = id
  f ^ˡ (suc n) = f ∘ (f ^ˡ n)

  _^ʳ_ : ∀ {a} {A : Set a} → (A → A) → ℕ → (A → A)
  f ^ʳ zero    = id
  f ^ʳ (suc n) = (f ^ˡ n) ∘ f


{-
  eq : ∀ {a} {A : Set a} (f : A → A) n → (f ^ˡ n) ≡ (f ^ʳ n)
  eq f zero    = refl
  eq f (suc n) = {!!}

  ff^≡f^f : ∀ {a} {A : Set a} (f : A → A) n x → f ((f ^ n) x) ≡ (f ^ n) (f x)
  ff^≡f^f f zero x    = refl
  ff^≡f^f f (suc n) x = cong f (ff^≡f^f f n x)
-}
