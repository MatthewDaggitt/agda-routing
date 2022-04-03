--------------------------------------------------------------------------------
-- Agda routing library
--
-- Properties of certified path algebras
--------------------------------------------------------------------------------

open import RoutingLib.Routing.Algebra

module RoutingLib.Routing.Algebra.Properties.CertifiedPathAlgebra
  {a b ℓ n} {algebra : RawRoutingAlgebra a b ℓ}
  (isRoutingAlgebra : IsRoutingAlgebra algebra)
  (isPathAlgebra : IsCertifiedPathAlgebra algebra n)
  where

open import Data.Nat using (suc; _≤_; _<_; s≤s)
open import Data.Product using (_×_; _,_; proj₁)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Fin using (Fin)
open import Function using (_∘_; _$_)
open import Relation.Nullary using (yes; no)
import Relation.Binary.Reasoning.Setoid as SetoidReasoning
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; inspect; [_]; refl; sym)
open import Relation.Unary using (Pred; Decidable)
open import Relation.Nullary.Negation using (contradiction)

open import RoutingLib.Routing.Basics.Path.CertifiedI
open import RoutingLib.Routing.Basics.Path.CertifiedI.Properties

open RawRoutingAlgebra algebra
open IsCertifiedPathAlgebra isPathAlgebra
open IsRoutingAlgebra isRoutingAlgebra

private
  variable
    i j : Fin n
    x y : PathWeight
    
--------------------------------------------------------------------------------
-- Path properties

p[∞]≈∅ : path ∞# ≈ₚ invalid
p[∞]≈∅ = r≈∞⇒path[r]≈∅ ≈-refl

p[0]≈[] : path 0# ≈ₚ trivial
p[0]≈[] = r≈0⇒path[r]≈[] ≈-refl

p[r]≡∅⇒f▷r≈∞ : ∀ (f : Step i j) → path x ≈ₚ invalid → f ▷ x ≈ ∞#
p[r]≡∅⇒f▷r≈∞ {x = x} f pᵣ≈∅ = begin
  f ▷ x  ≈⟨ ▷-cong f (path[r]≈∅⇒r≈∞ pᵣ≈∅) ⟩
  f ▷ ∞# ≈⟨ ▷-fixedPoint f ⟩
  ∞#     ∎
  where open SetoidReasoning S

p[f▷x]≈∅⊎↜ : ∀ (f : Step i j) x →
             (path (f ▷ x) ≈ₚ invalid) ⊎ (path (f ▷ x) ≈ₚ (i , j) ↜ path x)
p[f▷x]≈∅⊎↜ {i} {j} f x with f ▷ x ≟ ∞# | path x in eq
... | yes fx≈∞ | _       = inj₁ (r≈∞⇒path[r]≈∅ fx≈∞)
... | no  fx≉∞ | invalid = contradiction (p[r]≡∅⇒f▷r≈∞ f (≈ₚ-reflexive eq)) fx≉∞
... | no  fx≉∞ | valid q with (i , j) ⇿ᵥ? q | i ∉ᵥₚ? q
...   | no ¬ik⇿q | _       = inj₁ (r≈∞⇒path[r]≈∅ (path-reject f (≈ₚ-reflexive eq) (inj₁ ¬ik⇿q)))
...   | yes _    | no  i∈q = inj₁ (r≈∞⇒path[r]≈∅ (path-reject f (≈ₚ-reflexive eq) (inj₂ i∈q)))
...   | yes ik⇿q | yes i∉q = inj₂ (q , ≈ₚ-refl , ik⇿q , i∉q , path-accept f (≈ₚ-reflexive eq) fx≉∞ ik⇿q i∉q)

p[f▷x]≉[] : ∀ (f : Step i j) x → path (f ▷ x) ≉ₚ trivial
p[f▷x]≉[] f x p[fx]≈[] with p[f▷x]≈∅⊎↜ f x
... | inj₁ p[fx]≈∅                      = contradiction (≈ₚ-trans (≈ₚ-sym p[fx]≈∅)    p[fx]≈[]) λ()
... | inj₂ (_ , _ , _ , _ , p[fx]≈ij∷q) = contradiction (≈ₚ-trans (≈ₚ-sym p[fx]≈ij∷q) p[fx]≈[]) (λ {(valid ())})

▷-alignment : ∀ (f : Step i j) x {u v p e⇿p i∉p} →
              path (f ▷ x) ≈ₚ valid ((u , v) ∷ p ∣ e⇿p ∣ i∉p) →
              i ≡ u × j ≡ v × path x ≈ₚ valid p
▷-alignment {i} {j} f x p[fx]≈uv∷p with p[f▷x]≈∅⊎↜ f x
... | inj₁ p[fx]≈∅ = contradiction (≈ₚ-trans (≈ₚ-sym p[fx]≈∅) p[fx]≈uv∷p) λ()
... | inj₂ (q , p[x]≈q , _ , _ , p[fx]≈ij∷q)
  with ≈ₚ-trans (≈ₚ-sym p[fx]≈ij∷q) p[fx]≈uv∷p
...   | valid (refl ∷ p≈q) = refl , refl , ≈ₚ-trans p[x]≈q (valid p≈q)

--------------------------------------------------------------------------------
-- Source/destination properties

⇨[0]⇨ : ∀ i → i ⇨[ path 0# ]⇨ i 
⇨[0]⇨ i = ⇨[]⇨-resp-≈ₚ (≈ₚ-sym p[0]≈[]) (valid ⇨[]⇨)

⇨[∞]⇨ : ∀ i j → i ⇨[ path ∞# ]⇨ j 
⇨[∞]⇨ i j = ⇨[]⇨-resp-≈ₚ (≈ₚ-sym p[∞]≈∅) invalid

▷-pres-⇨[]⇨ : ∀ {i j k} (f : Step i j) x → j ⇨[ path x ]⇨ k → i ⇨[ path (f ▷ x) ]⇨ k
▷-pres-⇨[]⇨ {i} {j} {k} f x j⇨p[x]⇨k with p[f▷x]≈∅⊎↜ f x
... | inj₁ p[fx]≈∅                           = ⇨[]⇨-resp-≈ₚ (≈ₚ-sym p[fx]≈∅)    $ invalid
... | inj₂ (q , p[x]≈q , _ , _ , p[fx]≈ij∷q) = ⇨[]⇨-resp-≈ₚ (≈ₚ-sym p[fx]≈ij∷q) $ valid
  (⇨∷⇨ (drop-valid (⇨[]⇨-resp-≈ₚ p[x]≈q j⇨p[x]⇨k)))

--------------------------------------------------------------------------------
-- Size properties

size<n : 1 ≤ n → ∀ x → size x < n
size<n (s≤s _) _ = |p|<n (path _)

size≤n : ∀ x → size x ≤ n
size≤n r = |p|≤n (path r)

size-cong : x ≈ y → size x ≡ size y
size-cong x≈y = length-cong (path-cong x≈y)

--------------------------------------------------------------------------------
-- Weight properties

weight-cong : ∀ {A} {p q : Path n} → p ≈ₚ q → weight A p ≈ weight A q
weight-cong invalid              = ≈-refl
weight-cong (valid [])           = ≈-refl
weight-cong (valid (refl ∷ p≈q)) = ▷-cong _ (weight-cong (valid p≈q))
