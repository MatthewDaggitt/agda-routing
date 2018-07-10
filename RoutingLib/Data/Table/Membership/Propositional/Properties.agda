open import Algebra.FunctionProperties using (Op₂; Selective)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Nat.Properties using (⊓-sel; ⊔-sel)
open import Data.Fin using () renaming (zero to fzero; suc to fsuc)
open import Data.Product using (_,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; setoid)

open import RoutingLib.Data.Nat.Properties using (ℕₛ)
open import RoutingLib.Data.NatInf using (ℕ∞)
open import RoutingLib.Data.NatInf.Properties using () renaming (⊓-sel to ⊓∞-sel)
open import RoutingLib.Data.Table
import RoutingLib.Data.Table.Membership.Properties as Prop
open import RoutingLib.Data.Table.Membership.Propositional

module RoutingLib.Data.Table.Membership.Propositional.Properties where

  sel⇒foldr[t]∈t : ∀ {a} {A : Set a} {_•_ : Op₂ A} → Selective _≡_ _•_ →
                ∀ (e : A) {n} (t : Table A n) →
                foldr _•_ e t ≡ e ⊎ foldr _•_ e t ∈ t
  sel⇒foldr[t]∈t {A = A} = Prop.sel⇒foldr[t]∈t (setoid A)

  sel⇒foldr⁺[t]∈t : ∀ {a} {A : Set a} {_•_ : Op₂ A} → Selective _≡_ _•_ →
                 ∀ {n} (t : Table A (suc n)) → foldr⁺ _•_ t ∈ t
  sel⇒foldr⁺[t]∈t {A = A} = Prop.sel⇒foldr⁺[t]∈t (setoid A)

  max[t]∈t : ∀ ⊥ {n} (t : Table ℕ n) → max ⊥ t ≡ ⊥ ⊎ max ⊥ t ∈ t
  max[t]∈t = sel⇒foldr[t]∈t ⊔-sel

  min[t]∈t : ∀ ⊤ {n} (t : Table ℕ n) → min ⊤ t ≡ ⊤ ⊎ min ⊤ t ∈ t
  min[t]∈t = sel⇒foldr[t]∈t ⊓-sel

  min∞[t]∈t : ∀ ⊤ {n} (t : Table ℕ∞ n) → min∞ ⊤ t ≡ ⊤ ⊎ min∞ ⊤ t ∈ t
  min∞[t]∈t = sel⇒foldr[t]∈t ⊓∞-sel

  max⁺[t]∈t : ∀ {n} (t : Table ℕ (suc n)) → max⁺ t ∈ t
  max⁺[t]∈t = sel⇒foldr⁺[t]∈t ⊔-sel

  min⁺[t]∈t : ∀ {n} (t : Table ℕ (suc n)) → min⁺ t ∈ t
  min⁺[t]∈t = sel⇒foldr⁺[t]∈t ⊓-sel
