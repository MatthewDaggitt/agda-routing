open import Algebra using (Op₂; Selective)
open import Data.Nat using (ℕ; suc; zero; _<_; _≤_; s≤s; z≤n; _≟_)
open import Data.Nat.Properties using (⊔-sel; m≤m⊔n; ≤∧≢⇒<; ⊔-identityʳ; n≤m⊔n; ≤-trans)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.List
open import Data.List.Relation.Unary.Any as Any using (here; there)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Binary.Permutation.Propositional using (_↭_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (∃; _,_; _×_; proj₂)
open import Level using (Level)
open import Relation.Binary using (Setoid; Decidable; DecSetoid)
open import Relation.Binary.PropositionalEquality using (_≡_; setoid; refl; cong; cong₂)
open import Relation.Nullary using (yes; no)
open import Relation.Unary using () renaming (Decidable to Decidableᵤ)
open import Function using (_∘_; id)

open import RoutingLib.Data.List using (allFinPairs)
open import RoutingLib.Data.Nat.Properties using (ℕₛ)
import RoutingLib.Data.List.Membership.Setoid as SetoidMembership

module RoutingLib.Data.List.Membership.Propositional.Properties where

import RoutingLib.Data.List.Membership.Setoid.Properties as GM
import Data.List.Membership.Propositional.Properties as GM

private
  variable
    a b c : Level
    A : Set a
    B : Set b
    C : Set c

∈-upTo⁺ : ∀ {n i} → i < n → i ∈ upTo n
∈-upTo⁺ = GM.∈-applyUpTo⁺ id

∈-applyDownFrom⁺ : ∀ (f : ℕ → A) {n i} → i < n → f i ∈ applyDownFrom f n
∈-applyDownFrom⁺ f {suc n} {i} (s≤s i≤n) with i ≟ n
... | yes i≡n = here (cong f i≡n)
... | no  i≢n = there (∈-applyDownFrom⁺ f (≤∧≢⇒< i≤n i≢n))

∈-downFrom⁺ : ∀ {n i} → i < n → i ∈ downFrom n
∈-downFrom⁺ i<n = ∈-applyDownFrom⁺ id i<n

∈-allFin⁺ : ∀ {n} i → i ∈ allFin n
∈-allFin⁺ = GM.∈-tabulate⁺

∈-allFinPairs⁺ : ∀ {n} i j → (i , j) ∈ allFinPairs n
∈-allFinPairs⁺ i j = GM.∈-cartesianProduct⁺ (∈-allFin⁺ i) (∈-allFin⁺ j)
