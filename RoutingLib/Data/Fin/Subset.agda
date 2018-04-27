open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Fin.Subset
open import Data.Bool using (_≟_)
open import Data.Product using (∃; _×_; _,_)
open import Data.Vec using ([]; _∷_)
open import Relation.Nullary using (¬_)

open import RoutingLib.Data.Vec using (count)

module RoutingLib.Data.Fin.Subset where

  -- stdlib
  ∣_∣ : ∀ {n} → Subset n → ℕ
  ∣ p ∣ = count (_≟ inside) p

  _\\_ : ∀ {n} → Subset n → Subset n → Subset n
  []      \\ _             = []
  (x ∷ p) \\ (inside ∷ q)  = outside ∷ (p \\ q)
  (x ∷ p) \\ (outside ∷ q) = x       ∷ (p \\ q)


  Nonfull : ∀ {n} → Subset n → Set
  Nonfull p = ∃ λ i → i ∉ p
  
  Full : ∀ {n} → Subset n → Set
  Full p = ¬ (Nonfull p)
  
