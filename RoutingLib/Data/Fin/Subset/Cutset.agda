open import Data.Fin using (Fin)
open import Data.Fin.Dec using (_∈?_)
open import Data.Fin.Subset
open import Data.Fin.Subset.Properties using (∈⊤; ∉⊥)
open import Data.Nat using (_≤_)
open import Data.List using (List; []; filter; length)
open import Data.List.Properties using (filter-all; filter-notAll)
open import Data.List.Any.Membership.Propositional
  using (lose) renaming (_∈_ to _∈ₘ_)
open import RoutingLib.Data.List.Membership.Propositional.Properties using (∈-filter⁺)
open import Data.List.All using (All)
open import Data.List.All.Properties using (filter⁺₁)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Unary using (Decidable)
open import Relation.Nullary using (Dec; ¬_)
open import Relation.Nullary.Negation using (¬?)
open import Relation.Nullary.Product using (_×-dec_)

open import RoutingLib.Data.Fin.Subset using (Nonfull)
open import RoutingLib.Data.List using (allFinPairs)
open import RoutingLib.Data.List.All.Properties using (allFinPairs⁺)
open import RoutingLib.Data.List.Membership.Propositional.Properties
  using (∈-allFinPairs⁺)

module RoutingLib.Data.Fin.Subset.Cutset {n} where

  ------------------------------------------------------------------------------
  -- The "cuts" relation
  
  _↷_ : Fin n × Fin n → Subset n → Set
  (i , j) ↷ p = i ∉ p × j ∈ p

  _↷?_ : ∀ e p → Dec (e ↷ p)
  (i , j) ↷? p = (¬? (i ∈? p)) ×-dec (j ∈? p)

  ¬e↷⊤ : ∀ e → ¬ (e ↷ ⊤)
  ¬e↷⊤ (i , j) (i∉⊤ , _) = i∉⊤ ∈⊤

  ¬e↷⊥ : ∀ e → ¬ (e ↷ ⊥)
  ¬e↷⊥ (i , j) (_ , j∈⊥) = ∉⊥ j∈⊥
  
  ------------------------------------------------------------------------------
  -- Computing the cutset
  
  cutset : Subset n → List (Fin n × Fin n)
  cutset p = filter (_↷? p) (allFinPairs n)
  
  ∈cutset⇒↷ : ∀ p → All (_↷ p) (cutset p)
  ∈cutset⇒↷ p = filter⁺₁ (_↷? p) (allFinPairs n)

  ↷⇒∈cutset : ∀ {p e} → e ↷ p → e ∈ₘ cutset p
  ↷⇒∈cutset e↷p = ∈-filter⁺ (_↷? _) e↷p (∈-allFinPairs⁺ _ _)
  
  cutset[⊤]≡[] : cutset ⊤ ≡ []
  cutset[⊤]≡[] = filter-all (_↷? ⊤) (allFinPairs⁺ ¬e↷⊤)

  cutset[⊥]≡[] : cutset ⊥ ≡ []
  cutset[⊥]≡[] = filter-all (_↷? ⊥) (allFinPairs⁺ ¬e↷⊥)

  cutset-nonTrivial : ∀ {p} → Nonempty p → Nonfull p → 1 ≤ length (cutset p)
  cutset-nonTrivial {p} (i , i∈p) (j , j∉p) =
    filter-notAll (_↷? p) (lose (∈-allFinPairs⁺ j i) (j∉p , i∈p))
