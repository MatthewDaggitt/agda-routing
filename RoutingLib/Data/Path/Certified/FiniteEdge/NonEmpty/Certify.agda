open import Data.Fin using (Fin; fromℕ≤)
open import Data.List.Any using (here; there)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; _<_)
open import Data.Nat.Properties using (_<?_)
open import Data.Product using (Σ; _,_)
open import Data.Sum using (inj₁)
open import Function using (_∘_)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.PropositionalEquality using (_≢_; refl)

open import RoutingLib.Data.Fin.Properties using (fromℕ≤-injective)

open import RoutingLib.Data.Path.Certified.FiniteEdge.NonEmpty
open import RoutingLib.Data.Path.Certified.FiniteEdge.NonEmpty.Properties
open import RoutingLib.Data.Path.Uncertified.FiniteEdge.NonEmpty as U using ([]; _∷_; left; right)
open import RoutingLib.Data.Path.Uncertified.FiniteEdge.NonEmpty.Properties as Uₚ

module RoutingLib.Data.Path.Certified.FiniteEdge.NonEmpty.Certify {n : ℕ} where

mutual

  certify : U.Pathⁿᵗ n → Pathⁿᵗ n
  certify []            = []
  certify ((i , j) ∷ p) with i Uₚ.∈? p | (i , j) Uₚ.⇿? p
  ... | yes _    | _        = [] 
  ... | no  _    | no  _    = []
  ... | no  i∉p  | yes ij⇿p = (i , j) ∷ certify p ∣ ⇿-certify ij⇿p ∣ ∉-certify i∉p
  
  ⇿-certify : ∀ {p i j} → (i , j) U.⇿ p → (i , j) ⇿ certify p
  ⇿-certify {[]}          (U.start    i≢j) = start i≢j
  ⇿-certify {(j , k) ∷ p} (U.continue i≢j) with j Uₚ.∈? p | (j , k) Uₚ.⇿? p
  ... | yes _ | _        = start i≢j
  ... | no  _ | no  _    = start i≢j
  ... | no  _ | yes ij⇿p = continue i≢j

  ∉-certify : ∀ {p k} → k U.∉ p → k ∉ certify p
  ∉-certify {[]}          i∉p = notThere
  ∉-certify {(i , j) ∷ p} i∉p with i Uₚ.∈? p | (i , j) Uₚ.⇿? p
  ... | yes _ | _     = notThere
  ... | no  _ | no  _ = notThere
  ... | no  _ | yes _ = notHere (i∉p ∘ λ { refl → here left}) (i∉p ∘ (λ { refl → here right })) (∉-certify (i∉p ∘ there))

  certify-accept : ∀ {i j p} (ij⇿p : (i , j) U.⇿ p) (i∉p : i U.∉ p) →
                   certify ((i , j) ∷ p) ≈ₚ (i , j) ∷ certify p ∣ ⇿-certify ij⇿p ∣ ∉-certify i∉p
  certify-accept {i} {j} {p} ij⇿p i∉p with i Uₚ.∈? p | (i , j) Uₚ.⇿? p
  ... | yes i∈p | _        = contradiction i∈p i∉p
  ... | no  _   | no ¬ij⇿p = contradiction ij⇿p ¬ij⇿p
  ... | no  _   | yes _    = refl ∷ ≈ₚ-refl
