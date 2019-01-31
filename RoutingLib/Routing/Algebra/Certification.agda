--------------------------------------------------------------------------------
-- Proof that any algebra that is a path algebra is also a certified path
-- algebra. Certified path algebras are much easier to reason about as all nodes
-- are guaranteed to be members of the network and the path type itself contains
-- proofs that it is simple.
--------------------------------------------------------------------------------

open import Data.Nat using (ℕ)
open import RoutingLib.Routing.Algebra

module RoutingLib.Routing.Algebra.Certification
  {a b ℓ} {algebra : RawRoutingAlgebra a b ℓ}
  (isPathAlgebra : IsPathAlgebra algebra)
  (n : ℕ)
  where

open import Data.Fin using (Fin; toℕ)
open import Data.List using (_∷_)
open import Data.Maybe
open import Data.Product using (_,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (_∘_)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; inspect; [_]; subst)
import Relation.Binary.EqReasoning as EqReasoning
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Negation using (contradiction)

open import RoutingLib.Data.Path.Uncertified using ([]; _∷_)
open import RoutingLib.Data.Path.Uncertified.Properties using (_⇿?_; _∈ₚ?_)
open import RoutingLib.Data.Path.Uncertified.Certify
open import RoutingLib.Data.Path.CertifiedI
open import RoutingLib.Data.Path.CertifiedI.Properties hiding (_⇿?_)

open RawRoutingAlgebra algebra
open IsPathAlgebra isPathAlgebra

--------------------------------------------------------------------------------
-- Definition of a new path function that applies the `certify` function to any
-- valid path. The certify function effectively discards any part of the path
-- that is malformed or contains nodes not in the current network.

pathᶜ : Route → Maybe (Pathᵛ n)
pathᶜ r = map certify (path r)

--------------------------------------------------------------------------------
-- The key insight is that the required axioms that pathᶜ must only be obeyed
-- when extending the path in the `correct` matter hence the application of
-- certify does not affect the required axioms.

pathᶜ-cong : pathᶜ Preserves _≈_ ⟶ _≈ₚ_
pathᶜ-cong r≈s = ≈ₚ-reflexive (cong (map certify) (path-cong r≈s))

r≈0⇒pathᶜ[r]≈[] : ∀ {r} → r ≈ 0# → pathᶜ r ≈ₚ valid []
r≈0⇒pathᶜ[r]≈[] r≈0# rewrite r≈0⇒path[r]≈[] r≈0# = valid []

r≈∞⇒pathᶜ[r]≈∅ : {r : Route} → r ≈ ∞ → pathᶜ r ≈ₚ nothing
r≈∞⇒pathᶜ[r]≈∅ r≈∞ rewrite r≈∞⇒path[r]≈∅ r≈∞ = ≈ₚ-refl

pathᶜ[r]≈∅⇒r≈∞ : {r : Route} → pathᶜ r ≈ₚ nothing → r ≈ ∞
pathᶜ[r]≈∅⇒r≈∞ {r} p[r]≡∅ with path r | inspect path r
... | invalid | [ eq ] = path[r]≈∅⇒r≈∞ eq
... | valid p | _      = contradiction p[r]≡∅ λ()

pathᶜ-reject : ∀ {i j} {r p} (f : Step i j) → pathᶜ r ≈ₚ valid p →
               ¬ (i , j) ⇿ᵛ p ⊎ i ∈ᵥₚ p → f ▷ r ≈ ∞
pathᶜ-reject {r = r} {p} f p[r]≈p reason with path r | inspect path r | p[r]≈p
... | invalid | _      | ()
... | valid q | [ eq ] | valid qᶜ≈p with reason
...   | inj₁ ¬ij⇿p = path-reject f eq (inj₁ (¬ij⇿p ∘ ⇿ᵥ-resp-≈ᵥₚ qᶜ≈p ∘ ⇿-certify⁺ refl refl))
...   | inj₂ i∈p   = path-reject f eq (inj₂ (∈ₚ-certify⁻ refl (i∈p ∘ ∉ᵥₚ-resp-≈ᵥₚ qᶜ≈p)))

pathᶜ-accept : ∀ {i j r p} (f : Step i j) → pathᶜ r ≈ₚ valid p → f ▷ r ≉ ∞ →
               (ij⇿p : (i , j) ⇿ᵛ p) (i∉p : i ∉ᵥₚ p) →
               pathᶜ (f ▷ r) ≈ₚ valid ((i , j) ∷ p ∣ ij⇿p ∣ i∉p)
pathᶜ-accept {i} {j} {r} {p} f p[r]≈p fr≉∞ ij⇿p i∉p with path r | inspect path r | p[r]≈p
... | invalid | _      | ()
... | valid q | [ eq ] | valid qᶜ≈p with (toℕ i , toℕ j) ⇿? q | toℕ i ∈ₚ? q
...   | no ¬ij⇿q | _       = contradiction (path-reject f eq (inj₁ ¬ij⇿q)) fr≉∞
...   | yes _    | yes i∈q = contradiction (path-reject f eq (inj₂ i∈q)) fr≉∞
...   | yes ij⇿q | no  i∉q with path-accept f eq fr≉∞
...     | p[fr]≡ij∷q with path (f ▷ r) | inspect path (f ▷ r)
...       | invalid | [ eq' ] = contradiction (path[r]≈∅⇒r≈∞ eq') fr≉∞
...       | valid s | [ eq' ] with just-injective p[fr]≡ij∷q
...         | refl = valid (begin
  certify ((toℕ i , toℕ j) ∷ q)  ≈⟨ certify-accept ij⇿q i∉q ⟩
  ((i , j) ∷ certify q ∣ _ ∣ _ ) ≈⟨ refl ∷ qᶜ≈p ⟩
  ((i , j) ∷ p ∣ ij⇿p ∣ i∉p)     ∎)
  where open EqReasoning (ℙᵛₛ n)

certifiedPathAlgebra : IsCertifiedPathAlgebra algebra n
certifiedPathAlgebra = record
  { path             = pathᶜ
  ; path-cong        = pathᶜ-cong
  ; r≈0⇒path[r]≈[]   = r≈0⇒pathᶜ[r]≈[]
  ; r≈∞⇒path[r]≈∅    = r≈∞⇒pathᶜ[r]≈∅
  ; path[r]≈∅⇒r≈∞    = pathᶜ[r]≈∅⇒r≈∞
  ; path-reject      = pathᶜ-reject
  ; path-accept      = pathᶜ-accept
  }
