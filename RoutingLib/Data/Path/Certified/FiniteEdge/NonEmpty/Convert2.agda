open import Data.Fin using (Fin; fromℕ≤)
open import Data.List.Any using (here; there)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; _<_)
open import Data.Nat.Properties using (_<?_)
open import Data.Product using (Σ; _,_)
open import Data.Sum using (inj₁)
open import Function using (_∘_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≢_; refl)

open import RoutingLib.Data.Fin.Properties using (fromℕ≤-injective)

open import RoutingLib.Data.Path.Certified.FiniteEdge.NonEmpty
open import RoutingLib.Data.Path.Certified.FiniteEdge.NonEmpty.Sources
open import RoutingLib.Data.Path.Uncertified.FiniteEdge.NonEmpty as U using ([]; _∷_; left; right)
open import RoutingLib.Data.Path.Uncertified.FiniteEdge.NonEmpty.Properties as Uₚ

module RoutingLib.Data.Path.Certified.FiniteEdge.NonEmpty.Convert2 {n : ℕ} where

mutual

  to : U.Pathⁿᵗ n → Pathⁿᵗ n
  to []            = []
  to ((i , j) ∷ p) with i Uₚ.∈? p | (i , j) Uₚ.⇿? p
  ... | yes _    | _        = [] 
  ... | no  _    | no  _    = []
  ... | no  i∉p  | yes ij⇿p = (i , j) ∷ to p ∣ to-⇿ ij⇿p ∣ to-∉ i∉p
  
  to-⇿ : ∀ {p i j} → (i , j) U.⇿ p → (i , j) ⇿ to p
  to-⇿ {[]}          (U.start    i≢j) = start i≢j
  to-⇿ {(j , k) ∷ p} (U.continue i≢j) with j Uₚ.∈? p | (j , k) Uₚ.⇿? p
  ... | yes _ | _        = start i≢j
  ... | no  _ | no  _    = start i≢j
  ... | no  _ | yes ij⇿p = continue i≢j

  to-∉ : ∀ {p k} → k U.∉ p → k ∉ to p
  to-∉ {[]}          i∉p = notThere
  to-∉ {(i , j) ∷ p} i∉p with i Uₚ.∈? p | (i , j) Uₚ.⇿? p
  ... | yes _ | _     = notThere
  ... | no  _ | no  _ = notThere
  ... | no  _ | yes _ = notHere (i∉p ∘ λ { refl → here left}) (i∉p ∘ (λ { refl → here right })) (to-∉ (i∉p ∘ there))
