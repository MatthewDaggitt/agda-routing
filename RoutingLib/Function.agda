open import Function using (id; _∘_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (∃; _×_)

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

module RoutingLib.Function where

  -- Double composition
  
  _∘₂_ : ∀ {a b c d} → {A : Set a} {B : Set b} {C : Set c} {D : Set d} →
         (f : C → D) → (g : A → B → C) → (A → B → D) 
  f ∘₂ g = λ x y → f (g x y)


  -- Repeated application
  
  infix 7 _^ˡ_ _^ʳ_

  _^ˡ_ : ∀ {a} {A : Set a} → (A → A) → ℕ → (A → A)
  f ^ˡ zero    = id
  f ^ˡ (suc n) = f ∘ (f ^ˡ n)

  _^ʳ_ : ∀ {a} {A : Set a} → (A → A) → ℕ → (A → A)
  f ^ʳ zero    = id
  f ^ʳ (suc n) = (f ^ˡ n) ∘ f


  -- Pipelining

  -- stdlib
  infixl 0 _∣>_ _∣>′_

  -- stdlib
  _∣>_ : ∀ {a b} {A : Set a} {B : A → Set b} (x : A) (f : ∀ x → B x) → B x
  x ∣> f = f x

  -- stdlib
  _∣>′_ : ∀ {a b} {A : Set a} {B : Set b} (x : A) (f : A → B) → B
  _∣>′_ = _∣>_
