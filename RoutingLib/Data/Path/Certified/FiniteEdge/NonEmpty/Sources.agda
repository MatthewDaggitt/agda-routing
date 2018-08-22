open import Data.Maybe using (Maybe; nothing; just; Any)
open import Data.Nat using (ℕ)
open import Data.Product using (_,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

open import RoutingLib.Data.Path.Certified.FiniteEdge.NonEmpty
open import RoutingLib.Data.Path.Certified.FiniteEdge.NonEmpty.Properties

module RoutingLib.Data.Path.Certified.FiniteEdge.NonEmpty.Sources {n : ℕ} where


source : ∀ {n} → Pathⁿᵗ n → Maybe (Vertex n)
source []                    = nothing
source ((i , j) ∷ p ∣ _ ∣ _) = just i

--------------------------------------
-- Replacing the source node of a path

Replacable : Vertex n → Pathⁿᵗ n → Set
Replacable k p = Any (k ≡_) (source p) ⊎ k ∉ p

⇿-replacable : {p : Pathⁿᵗ n} → ∀ {i j} → (i , j) ⇿ p → Replacable j p
⇿-replacable (start x)    = inj₂ notThere
⇿-replacable (continue x) = inj₁ (just refl)

replace : ∀ {k p} → Replacable k p → Pathⁿᵗ n
replace {_} {[]}                       _                          = []
replace {_} {p}                        (inj₁ _)                   = p
replace {k} {(i , j) ∷ p ∣ ij⇿p ∣ i∉p} (inj₂ (notHere _ k≢j k∉p)) = (k , j) ∷ p ∣ ⇿-sub ij⇿p k≢j ∣ k∉p

replace-∉ : ∀ {k} {p : Pathⁿᵗ n} (k↝p : Replacable k p) → ∀ {l} → l ∉ p → l ≢ k → l ∉ replace k↝p
replace-∉ {_} {[]}                      x                      l∉p                 l≢k = l∉p
replace-∉ {_} {(i , j) ∷ p ∣ e⇿p ∣ e∉p} (inj₁ (just refl))     (notHere _ l≢j l∉p) l≢k = notHere l≢k l≢j l∉p
replace-∉ {_} {(i , j) ∷ p ∣ e⇿p ∣ e∉p} (inj₂ (notHere _ _ _)) (notHere _ l≢j l∉p) l≢k = notHere l≢k l≢j l∉p

replace-⇿ : ∀ {k} {p : Pathⁿᵗ n} (k↝p : Replacable k p) → ∀ {l} → l ≢ k → (l , k) ⇿ replace k↝p
replace-⇿ {_} {[]}                _                      l≢k = start l≢k
replace-⇿ {_} {e ∷ p ∣ e⇿p ∣ e∉p} (inj₁ (just refl))     l≢k = continue l≢k
replace-⇿ {_} {e ∷ p ∣ e⇿p ∣ e∉p} (inj₂ (notHere _ _ _)) l≢k = continue l≢k
