

module RoutingLib.Data.Path.Uncertified.Choice where

open import Algebra.FunctionProperties
open import Algebra.Construct.NaturalChoice.Min as Min
open import Data.Sum
open import Relation.Binary.PropositionalEquality

open import RoutingLib.Data.Path.Uncertified
open import RoutingLib.Data.Path.Uncertified.Properties

abstract

  open module Minₗₑₓ = Min ≤ₗₑₓ-totalOrder public
    renaming
    ( _⊓_     to _⊓ₗₑₓ_
    ; ⊓-sel   to ⊓ₗₑₓ-sel
    ; ⊓-comm  to ⊓ₗₑₓ-comm
    ; ⊓-assoc to ⊓ₗₑₓ-assoc
    ; ⊓-magma to ⊓ₗₑₓ-magma
    )

  ⊓ₗₑₓ-zeroʳ : RightZero _≡_ [] _⊓ₗₑₓ_
  ⊓ₗₑₓ-zeroʳ = Minₗₑₓ.⊓-zeroʳ ≤ₗₑₓ-minimum

min-distrib : ∀ (f : Path → Path) → (∀ {x} {y} → x ≤ₗₑₓ y →  f x ≤ₗₑₓ f y) → ∀ x y → f(x ⊓ₗₑₓ y) ≡ f x ⊓ₗₑₓ f y
min-distrib f mono x y with ≤ₗₑₓ-total x y | ≤ₗₑₓ-total (f x) (f y)
min-distrib f mono x y | inj₁ x≤y | inj₁ fx≤fy = refl
min-distrib f mono x y | inj₁ x≤y | inj₂ fy≤fx = ≤ₗₑₓ-antisym (mono  x≤y) fy≤fx 
min-distrib f mono x y | inj₂ y≤x | inj₁ fx≤fy = ≤ₗₑₓ-antisym (mono y≤x) fx≤fy
min-distrib f mono x y | inj₂ y≤x | inj₂ fy≤fx = refl 

∷-distrib-⊓ₗₑₓ : ∀ e p q → e ∷ (p ⊓ₗₑₓ q) ≡ (e ∷ p) ⊓ₗₑₓ (e ∷ q)
∷-distrib-⊓ₗₑₓ e p q = min-distrib _ (∷-mono-≤ₗₑₓ e) p q
