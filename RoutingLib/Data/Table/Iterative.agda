open import Data.Fin using (Fin; compare; equal; less; greater)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)

open import RoutingLib.Data.NatInf using (ℕ∞)
open import RoutingLib.Data.Table
open import RoutingLib.Data.Table.Membership.Propositional.Properties

module RoutingLib.Data.Table.Iterative where

  exclude : ∀ {n} → ℕ∞ → Table ℕ∞ n → Fin n → Table ℕ∞ n
  exclude ⊤ t i j with compare i j
  ... | equal     _  = ⊤
  ... | less    _ _ = t j
  ... | greater _ _ = t j

  k-min∞ : ∀ {n} → ℕ → ℕ∞ → Table ℕ∞ n → ℕ∞
  k-min∞ zero ⊤ t = min∞ ⊤ t
  k-min∞ (suc k) ⊤ t with min∞[t]∈t ⊤ t
  ... | inj₁ min≡⊤ = ⊤
  ... | inj₂ (i , _) = k-min∞ k ⊤ (exclude ⊤ t i)
