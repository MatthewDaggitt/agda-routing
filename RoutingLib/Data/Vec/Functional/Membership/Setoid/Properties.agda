open import Algebra using (Op₂; Selective)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using () renaming (zero to fzero; suc to fsuc)
open import Data.Sum using (_⊎_; inj₁; inj₂) renaming (map to mapₛ)
open import Data.Product using (_,_)
open import Data.Vec.Functional
open import Function using (_∘_)
open import Relation.Binary using (Setoid)

open import RoutingLib.Data.Vec.Functional
import RoutingLib.Data.Vec.Functional.Membership as Membership

module RoutingLib.Data.Vec.Functional.Membership.Setoid.Properties {a ℓ} (S : Setoid a ℓ) where

open Membership S
open Setoid S renaming (Carrier to A)

sel⇒foldr[t]∈t : ∀ {_•_} → Selective _≈_ _•_ → ∀ e {n} (t : Vector A n) →
              foldr _•_ e t ≈ e ⊎ foldr _•_ e t ∈ t
sel⇒foldr[t]∈t sel e {zero}  t = inj₁ refl
sel⇒foldr[t]∈t sel e {suc n} t with sel (t fzero) (foldr _ e (t ∘ fsuc))
... | inj₁ t₀•f≈t₀ = inj₂ (fzero , t₀•f≈t₀)
... | inj₂ t₀•f≈f  with sel⇒foldr[t]∈t sel e (t ∘ fsuc)
...   | inj₁ f≈e        = inj₁ (trans t₀•f≈f f≈e)
...   | inj₂ (i , f≈tᵢ) = inj₂ (fsuc i , trans t₀•f≈f f≈tᵢ)

sel⇒foldr⁺[t]∈t : ∀ {_•_} → Selective _≈_ _•_ →
               ∀ {n} (t : Vector A (suc n)) → foldr⁺ _•_ t ∈ t
sel⇒foldr⁺[t]∈t sel {zero}  t = fzero , refl
sel⇒foldr⁺[t]∈t sel {suc n} t with sel (t fzero) (foldr⁺ _ (t ∘ fsuc))
... | inj₁ t₀•f≈t₀ = fzero , t₀•f≈t₀
... | inj₂ t₀•f≈f  with sel⇒foldr⁺[t]∈t sel (t ∘ fsuc)
...   | (i , f≈tᵢ) = fsuc i , trans t₀•f≈f f≈tᵢ
