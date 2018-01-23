open import Data.Fin using (Fin; compare; equal; less; greater)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Product using (_,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; _≢_)

open import RoutingLib.Data.NatInf using (ℕ∞)
open import RoutingLib.Data.Table
open import RoutingLib.Data.Table.Iterative
import RoutingLib.Data.Table.Membership.Properties as Prop
open import RoutingLib.Data.Table.Membership.Propositional

module RoutingLib.Data.Table.Iterative.Properties where

  exclude[t]⊆t : ∀ {n} ⊤ (t : Table ℕ∞ n) i x → x ∈ exclude ⊤ t i → x ≡ ⊤ ⊎ x ∈ t
  exclude[t]⊆t ⊤ t i x (j , xⱼ∈exclude) with compare i j
  ... | equal     _ = inj₁ xⱼ∈exclude
  ... | less    _ _ = inj₂ (j , xⱼ∈exclude)
  ... | greater _ _ = inj₂ (j , xⱼ∈exclude)

  postulate k-min∞-sel : ∀ {n} k ⊤ (t : Table ℕ∞ n) → k-min∞ k ⊤ t ≡ ⊤ ⊎ k-min∞ k ⊤ t ≢ k-min∞ (suc k) ⊤ t

  postulate k-min∞-⊤ : ∀ {n} k ⊤ (t : Table ℕ∞ n) → k-min∞ k ⊤ t ≡ ⊤ → ∀ k' → k-min∞ (k + k') ⊤ t ≡ ⊤
