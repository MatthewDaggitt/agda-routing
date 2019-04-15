module RoutingLib.Data.Fin.Subset.Cutset {n} where

open import Data.Fin using (Fin)
open import Data.Fin.Dec using (_∈?_)
open import Data.Fin.Subset
open import Data.Fin.Subset.Properties using (∈⊤; ∉⊥)
open import Data.Nat using (_≤_)
open import Data.List using (List; []; filter; length)
open import Data.List.Properties using (filter-none; filter-some)
open import Data.List.Membership.Propositional
  using (lose) renaming (_∈_ to _∈ₘ_)
open import Data.List.Membership.Propositional.Properties using (∈-filter⁺)
open import Data.List.All using (All)
open import Data.List.All.Properties using (all-filter)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Unary using (Decidable)
open import Relation.Nullary using (Dec; ¬_)
open import Relation.Nullary.Negation using (¬?)
open import Relation.Nullary.Product using (_×-dec_)

open import RoutingLib.Data.Fin.Subset using (Nonfull)
open import RoutingLib.Data.Fin.Subset.Properties using (Nonfull-witness)
open import RoutingLib.Data.List using (allFinPairs)
open import RoutingLib.Data.List.Relation.Unary.All.Properties using (allFinPairs⁺)
open import RoutingLib.Data.List.Membership.Propositional.Properties
  using (∈-allFinPairs⁺)

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
∈cutset⇒↷ p = all-filter (_↷? p) (allFinPairs n)

↷⇒∈cutset : ∀ {p e} → e ↷ p → e ∈ₘ cutset p
↷⇒∈cutset e↷p = ∈-filter⁺ (_↷? _) (∈-allFinPairs⁺ _ _) e↷p

cutset[⊤]≡[] : cutset ⊤ ≡ []
cutset[⊤]≡[] = filter-none (_↷? ⊤) (allFinPairs⁺ ¬e↷⊤)

cutset[⊥]≡[] : cutset ⊥ ≡ []
cutset[⊥]≡[] = filter-none (_↷? ⊥) (allFinPairs⁺ ¬e↷⊥)

cutset-nonTrivial : ∀ {p} → Nonempty p → Nonfull p → 1 ≤ length (cutset p)
cutset-nonTrivial {p} (i , i∈p) ¬pᶠ with Nonfull-witness ¬pᶠ
... | (j , j∉p) = filter-some (_↷? p) (lose (∈-allFinPairs⁺ j i) (j∉p , i∈p))
