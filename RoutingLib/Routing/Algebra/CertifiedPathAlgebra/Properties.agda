open import Data.Nat using (suc; _≤_; _<_; s≤s)
open import Data.Product using (_,_; proj₁)
open import Data.Sum using (inj₁; inj₂)
open import Data.Fin using (Fin)
open import Function using (_∘_)
open import Relation.Nullary using (yes; no)
import Relation.Binary.EqReasoning as EqReasoning
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; inspect; [_]; refl; sym)
open import Relation.Unary using (Decidable)
open import Relation.Nullary.Negation using (contradiction)

open import RoutingLib.Data.Path.CertifiedI
open import RoutingLib.Data.Path.CertifiedI.Properties

open import RoutingLib.Routing.Algebra
open import RoutingLib.Routing.Algebra.CertifiedPathAlgebra
import RoutingLib.Routing.Algebra.RoutingAlgebra.Properties as RoutingAlgebraProperties

module RoutingLib.Routing.Algebra.CertifiedPathAlgebra.Properties
  {a b ℓ n} (algebra : RawRoutingAlgebra a b ℓ)
  (isPathAlgebra : IsCertifiedPathAlgebra algebra n)
  where

open RawRoutingAlgebra algebra
open IsCertifiedPathAlgebra isPathAlgebra

--------------------------------------------------------------------------------
-- Import routing algebra properties

open RoutingAlgebraProperties algebra isRoutingAlgebra public

--------------------------------------------------------------------------------
-- Path properties

p[∞]≈∅ : path ∞ ≈ₚ invalid
p[∞]≈∅ = r≈∞⇒path[r]≈∅ ≈-refl

p[0]≈[] : path 0# ≈ₚ valid []
p[0]≈[] = r≈0⇒path[r]≈[] ≈-refl

p[r]≡∅⇒f▷r≈∞ : ∀ {i j : Fin n} (f : Step i j) {r} → path r ≡ invalid → f ▷ r ≈ ∞
p[r]≡∅⇒f▷r≈∞ f {r} pᵣ≡∅ = begin
  f ▷ r ≈⟨ ▷-cong f (path[r]≈∅⇒r≈∞ (≈ₚ-reflexive pᵣ≡∅)) ⟩
  f ▷ ∞ ≈⟨ ▷-fixedPoint f ⟩
  ∞     ∎
  where open EqReasoning S

--------------------------------------------------------------------------------
-- Size properties

size<n : 1 ≤ n → ∀ r → size r < n
size<n (s≤s _) r = |p|<n (path _)

size≤n+1 : ∀ r → size r ≤ suc n
size≤n+1 r = |p|≤1+n (path r)

size-cong : ∀ {r s} → r ≈ s → size r ≡ size s
size-cong {r} {s} r≈s = length-cong (path-cong r≈s)
