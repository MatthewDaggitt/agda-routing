open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import Function using (_∘_)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.PropositionalEquality using (inspect; [_])
import Relation.Binary.EqReasoning as EqReasoning

open import RoutingLib.Data.Path.Certified.FiniteEdge
open import RoutingLib.Data.Path.Certified.FiniteEdge.Properties using (≈ₚ-reflexive; ≈ₚ-sym; p≉i∷p; ℙₛ)
open import RoutingLib.Data.Path.Certified.FiniteEdge.NonEmpty.Properties using (_⇿?_; _∉?_)

open import RoutingLib.Routing.Algebra
import RoutingLib.Routing.Algebra.Properties.PathAlgebra
  as PathAlgebraProperties

module RoutingLib.Routing.Algebra.Properties.IncreasingPathAlgebra
  {a b ℓ n} (algebra : IncreasingPathAlgebra a b ℓ n) where

open IncreasingPathAlgebra algebra

--------------------------------------------------------------------------------
-- Open path algebra properties

open PathAlgebraProperties pathAlgebra public

▷-strictlyIncreasing : ∀ i k {x} → x ≉ ∞ → x <₊ A i k ▷ x
▷-strictlyIncreasing i k {x} x≉∞ with A i k ▷ x ≟ ∞
... | yes Aᵢₖx≈∞ = ≈-trans (⊕-cong Aᵢₖx≈∞ ≈-refl) (⊕-identityˡ x) , x≉∞ ∘ (λ x≈Aᵢₖx → ≈-trans x≈Aᵢₖx Aᵢₖx≈∞)
... | no  Aᵢₖx≉∞ with path x | inspect path x
...   | invalid | [ p[x]≡∅ ] = contradiction (path[r]≈∅⇒r≈∞ (≈ₚ-reflexive p[x]≡∅)) x≉∞
...   | valid p | [ p[x]≡p ] with (i , k) ⇿? p | i ∉? p
...     | no ¬e⇿p | _       = contradiction (path-reject (≈ₚ-reflexive p[x]≡p) (inj₁ ¬e⇿p)) Aᵢₖx≉∞
...     | _       | no  i∈p = contradiction (path-reject (≈ₚ-reflexive p[x]≡p) (inj₂ i∈p)) Aᵢₖx≉∞
...     | yes e⇿p | yes i∉p = (▷-increasing (A i k) x) ,
  λ x≈Aik▷x → p≉i∷p (begin
    valid p                      ≈⟨ ≈ₚ-sym (≈ₚ-reflexive p[x]≡p) ⟩
    path x                       ≈⟨ path-cong x≈Aik▷x ⟩
    path (A i k ▷ x)             ≈⟨ path-accept (≈ₚ-reflexive p[x]≡p) Aᵢₖx≉∞ e⇿p i∉p ⟩
    valid ((i , k) ∷ p ∣ _ ∣ _) ∎)
  where open EqReasoning (ℙₛ n)
