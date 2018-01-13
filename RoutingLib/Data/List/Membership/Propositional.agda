open import Data.Nat using (ℕ; suc; zero; _<_; _≤_; s≤s; z≤n; _≟_)
open import Data.Nat.Properties using (⊔-sel; m≤m⊔n; ≤+≢⇒<; ⊔-identityʳ; n≤m⊔n; ≤-trans)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.List
open import Data.List.Any as Any using (here; there)
open import Data.List.Any.Membership.Propositional using (_∈_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (∃; _,_; _×_; proj₂)
open import Relation.Binary using (Setoid; Decidable; DecSetoid)
open import Relation.Binary.PropositionalEquality using (_≡_; setoid; refl; cong; cong₂)
open import Relation.Binary.List.Pointwise using (≡⇒Rel≡)
open import Relation.Nullary using (yes; no)
open import Function using (_∘_; id)

open import RoutingLib.Data.List using (combine; applyBetween; between; allFinPairs)
open import RoutingLib.Data.Nat.Properties using (ℕₛ)
open import RoutingLib.Data.List.Permutation using (_⇿_)
import RoutingLib.Data.List.Membership.Setoid as SetoidMembership

module RoutingLib.Data.List.Membership.Propositional {a} {A : Set a} (_≟_ : Decidable (_≡_ {A = A})) where

  --open import RoutingLib.Data.List.Membership public

