open import Data.Nat
open import Data.Nat.Properties using (≤-trans; n≤1+n)
open import Data.Product using (∃; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Unary using (Pred)

module RoutingLib.Data.Range where

--------------------------------------------------------------------------------
-- Type and constructors

record Range : Set where
  constructor [_,_]
  field
    start : ℕ
    end   : ℕ

⟨_,_] : ℕ → ℕ → Range
⟨ s , e ] = [ suc s , e ]


--------------------------------------------------------------------------------
-- Membership

_∈_ : ℕ → Range → Set
t ∈ [ s , e ] = s ≤ t × t ≤ e

--------------------------------------------------------------------------------
-- Predicates

All : ∀ {p} → Pred ℕ p → Pred Range p
All P r = ∀ {t} → t ∈ r → P t

Any : ∀ {p} → Pred ℕ p → Pred Range p
Any P r = ∃ λ t → t ∈ r × P t

--------------------------------------------------------------------------------
-- Properties

occupied : ∀ {x s e} → x ∈ [ s , e ] → s ≤ e
occupied (s≤x , x≤e) = ≤-trans s≤x x≤e

∈-growʳ : ∀ {x s e₁ e₂} → e₁ ≤ e₂ → x ∈ [ s , e₁ ] → x ∈ [ s , e₂ ]
∈-growʳ e₁≤e₂ (s≤x , x≤e₁) = s≤x , (≤-trans x≤e₁ e₁≤e₂)

∈-growʳ₁ : ∀ {x s e} → x ∈ [ s , e ] → x ∈ [ s , suc e ]
∈-growʳ₁ = ∈-growʳ (n≤1+n _)
