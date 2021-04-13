open import Data.Nat using (ℕ; zero; suc) renaming (_<′_ to _<'ℕ_; _≤′_ to _≤'ℕ_)
open import Data.Nat.Properties using () renaming (≤-refl to ≤ℕ-refl; ≤⇒≤′ to ≤⇒≤'ℕ)
open import Data.Nat.Induction using () renaming (<′-wellFounded to <'ℕ-wellFounded)
open import Induction.WellFounded as wf
open import Relation.Binary.PropositionalEquality using (refl)

open import RoutingLib.Data.NatInf
open import RoutingLib.Data.NatInf.Properties

module RoutingLib.Data.NatInf.WellFounded where

-- Complete induction based on _<'_
from-<'ℕwf : ∀ {n} → Acc _<'ℕ_ n → WfRec _<'_ (Acc _<'_) (N n)
from-<'ℕwf {suc n} (acc rs) (N n) ≤'-refl       = acc (from-<'ℕwf (rs n (≤⇒≤'ℕ ≤ℕ-refl)))
from-<'ℕwf {suc n} (acc rs) (N x) (≤'-step x<n) = acc (from-<'ℕwf (rs x (≤'⇒≤'ℕ (≤'-step x<n))))


mutual
  <'-well-founded : WellFounded _<'_
  <'-well-founded n = acc (<'-well-founded' n)

  <'-well-founded' : ∀ n → WfRec _<'_ (Acc _<'_) n
  <'-well-founded' ∞ ∞ ()
  <'-well-founded' ∞ (N m) ≤'-∞ = acc (from-<'ℕwf (<'ℕ-wellFounded m))
  <'-well-founded' (N x) ∞ ()
  <'-well-founded' (N .(suc m)) (N m) ≤'-refl = <'-well-founded (N m)
  <'-well-founded' (N (suc n)) (N m) (≤'-step m<n) = <'-well-founded' (N n) (N m) m<n
