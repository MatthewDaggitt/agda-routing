open import Relation.Binary

open import Data.Fin.Subset
open import Data.Fin.Subset.Properties
open import Data.Nat.Induction
open import Data.Nat using (ℕ; zero; suc; z≤n; s≤s; _<_; _≤_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; n≤1+n)
open import Data.Product as Prod
open import Level using (Level; _⊔_)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality as P using (_≢_; _≡_; subst)
open import Relation.Binary.Construct.Closure.Transitive
open import Relation.Nullary using (¬_; Dec; yes; no)
import Relation.Nullary.Decidable as Dec
open import Relation.Nullary
open import Relation.Unary as U using (Pred)

open import RoutingLib.Data.Fin.Subset
open import RoutingLib.Data.Fin.Subset.Properties

module RoutingLib.Relation.Binary.Construct.Closure.Transitive.Any
  {a r} {A : Set a} {R : Rel A r}
  where

private
  R⁺ = TransClosure R

private
  variable
    p : Level
    x y z : A

------------------------------------------------------------------------
-- Definitions

data AnyEdge (P : ∀ {x y : A} → R x y → Set p) : ∀ {x y} → R⁺ x y → Set (a ⊔ p ⊔ r) where
  here₁  : {Rxy : R x y}                 → P Rxy → AnyEdge P [ Rxy ]
  here₂  : {Rxy : R x y} {R⁺yz : R⁺ y z} → P Rxy → AnyEdge P (Rxy ∷ R⁺yz)
  there  : {Rxy : R x y} {R⁺yz : R⁺ y z} → AnyEdge P R⁺yz → AnyEdge P (Rxy ∷ R⁺yz)

AnyNode : (P : A → Set p) → (∀ {x y} → R⁺ x y → Set (a ⊔ p ⊔ r))
AnyNode P = AnyEdge (λ {x} _ → P x)

------------------------------------------------------------------------
-- Properties

anyEdge? : {P : ∀ {x y : A} → R x y → Set p} →
           (∀ {x y} → (Rxy : R x y) → Dec (P Rxy)) →
           ∀ {x y} → (R⁺xy : R⁺ x y) → Dec (AnyEdge P R⁺xy)
anyEdge? P? [ Rxy ] with P? Rxy
... | yes PRxy = yes (here₁ PRxy)
... | no ¬PRxy = no λ { (here₁ PRxy) → ¬PRxy PRxy}
anyEdge? P? (Rxy ∷ R⁺yz) with P? Rxy
... | yes PRxy = yes (here₂ PRxy)
... | no ¬PRxy with anyEdge? P? R⁺yz
...   | yes PR⁺yz = yes (there PR⁺yz)
...   | no ¬PR⁺yz = no λ
  { (here₂ PRxy)  → ¬PRxy PRxy
  ; (there PR⁺yz) → ¬PR⁺yz PR⁺yz
  }

anyNode? : {P : A → Set p} → U.Decidable P →
           ∀ {x y} → (R⁺xy : R⁺ x y) → Dec (AnyNode P R⁺xy)
anyNode? P? = anyEdge? (λ {x} _ → P? x)
