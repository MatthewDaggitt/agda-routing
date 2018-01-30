open import Data.Nat using (ℕ; zero; suc; _<_)
open import Data.Fin using (Fin; zero)
open import Data.Fin.Subset
open import Data.Bool using (_≟_)
open import Data.Vec using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)


open import RoutingLib.Data.Vec using (count)

module RoutingLib.Data.Fin.Subset where

  size : ∀ {n} → Subset n → ℕ
  size p = count (_≟ inside) p

  _\\_ : ∀ {n} → Subset n → Subset n → Subset n
  []      \\ _             = []
  (x ∷ p) \\ (inside ∷ q)  = outside ∷ (p \\ q)
  (x ∷ p) \\ (outside ∷ q) = x       ∷ (p \\ q)
  
  postulate size[p\\q]<size[p] : ∀ {n} {p q : Subset n} → Nonempty (p ∩ q) → size (p \\ q) < size p

  postulate i∉p⇒i∉p\\q : ∀ {n} {p : Subset n} {i} → i ∉ p → ∀ q → i ∉ p \\ q

  postulate i∉p\\q⇒i∉p : ∀ {n} {p q : Subset n} {i} → i ∉ p \\ q → i ∉ q → i ∉ p

  postulate i∉⁅j⁆ : ∀ {n} {i j : Fin n} → i ≢ j → i ∉ ⁅ j ⁆ 
