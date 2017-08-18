open import Algebra.FunctionProperties using (Op₂; Selective)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Nat.Properties using (⊔-sel; ⊓-sel)
open import Data.Sum using (_⊎_)
open import Relation.Binary.PropositionalEquality using (_≡_; setoid)

open import RoutingLib.Data.Matrix
open import RoutingLib.Data.Matrix.Membership.Propositional
import RoutingLib.Data.Matrix.Membership.Properties as Prop

module RoutingLib.Data.Matrix.Membership.Propositional.Properties where

  sel⇒fold[M]∈M : ∀ {a} {A : Set a} {_•_ : Op₂ A} → Selective _≡_ _•_ →
                    ∀ (e : A) {m n} (M : Matrix A m n) →
                    fold _•_ e M ≡ e ⊎ fold _•_ e M ∈ M
  sel⇒fold[M]∈M = Prop.sel⇒fold[M]∈M (setoid _)
    
  sel⇒fold⁺[M]∈M : ∀ {a} {A : Set a} {_•_ : Op₂ A} → Selective _≡_ _•_ →
                     ∀ {m n} (M : Matrix A (suc m) (suc n)) →
                     fold⁺ _•_ M ∈ M
  sel⇒fold⁺[M]∈M = Prop.sel⇒fold⁺[M]∈M (setoid _)
    
  min⁺[M]∈M : ∀ {m n} (M : Matrix ℕ (suc m) (suc n)) → min⁺ M ∈ M
  min⁺[M]∈M = sel⇒fold⁺[M]∈M ⊓-sel
  
  max⁺[M]∈M : ∀ {m n} (M : Matrix ℕ (suc m) (suc n)) → max⁺ M ∈ M
  max⁺[M]∈M = sel⇒fold⁺[M]∈M ⊔-sel
