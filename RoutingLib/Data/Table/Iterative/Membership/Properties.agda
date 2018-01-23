open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import RoutingLib.Data.NatInf using (ℕ∞)
open import RoutingLib.Data.Table
open import RoutingLib.Data.Table.Iterative
import RoutingLib.Data.Table.Membership.Properties as Prop
open import RoutingLib.Data.Table.Membership.Propositional
open import RoutingLib.Data.Table.Membership.Propositional.Properties

module RoutingLib.Data.Table.Iterative.Membership.Properties where

  postulate k-min∞[t]∈t : ∀ k ⊤ {n} (t : Table ℕ∞ n) → k-min∞ k ⊤ t ≡ ⊤ ⊎ k-min∞ k ⊤ t ∈ t
{-  k-min∞[t]∈t zero ⊤ t   = min∞[t]∈t ⊤ t
  k-min∞[t]∈t (suc k) ⊤ t with min∞[t]∈t ⊤ t
  ... | inj₁ min≡⊤ = inj₁ refl
  ... | inj₂ (i , min≡tᵢ) = inj₂ (i , {!!})-}

{-
  min∞[t]∈t : ∀ ⊤ {n} (t : Table ℕ∞ n) → min∞ ⊤ t ≡ ⊤ ⊎ min∞ ⊤ t ∈ t
  min∞[t]∈t = sel⇒foldr[t]∈t ⊓∞-sel

exclude[t]⊆t : ∀ {n} ⊤ (t : Table ℕ∞ n) i x → x ∈ exclude ⊤ t i → x ≡ ⊤ ⊎ x ∈ t
  exclude[t]⊆t ⊤ t i x (j , xⱼ∈exclude) with compare i j
  ... | equal     _ = inj₁ xⱼ∈exclude
  ... | less    _ _ = inj₂ (j , xⱼ∈exclude)
  ... | greater _ _ = inj₂ (j , xⱼ∈exclude)
  

-}
