open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin; zero; suc)
open import Data.Fin.Subset
open import Data.Bool using (_≟_)
open import Data.Product using (∃; _×_; _,_)
open import Data.Vec using ([]; _∷_)
open import Function using (_∘_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_)

module RoutingLib.Data.Fin.Subset where

_\\_ : ∀ {n} → Subset n → Subset n → Subset n
[]      \\ _             = []
(x ∷ p) \\ (inside ∷ q)  = outside ∷ (p \\ q)
(x ∷ p) \\ (outside ∷ q) = x       ∷ (p \\ q)

Full : ∀ {n} → Subset n → Set
Full p = ∀ i → i ∈ p

Nonfull : ∀ {n} → Subset n → Set
Nonfull p = ¬ (Full p)
