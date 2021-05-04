
open import Data.List hiding (_∷ʳ_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat using (_<_; z≤n; s≤s)
open import Data.Product using (_×_; _,_)
open import Data.Empty.Irrelevant using (⊥-elim)
open import Function using (_∘_)
open import Level using (Level)
open import Relation.Unary using (Pred; Decidable)
  renaming (_∈_ to _∈ᵤ_; _∉_ to _∉ᵤ_; _⊆_ to _⊆ᵤ_)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary using (Setoid; _Respects_)

module RoutingLib.Data.List.Relation.Binary.Sublist.Setoid.Properties
  {a ℓ} (S : Setoid a ℓ) where

open Setoid S renaming (Carrier to A)

open import Data.List.Relation.Binary.Sublist.Setoid S
open import Data.List.Relation.Binary.Sublist.Setoid.Properties S
open import Data.List.Relation.Binary.Equality.Setoid S hiding (filter⁺)
open import Data.List.Membership.Setoid S

open import RoutingLib.Data.List.Relation.Binary.Sublist.Setoid S

private
  variable
    p q : Level

module _ {P : Pred A p} (P? : Decidable P) (P-resp-≈ : P Respects _≈_)
         {Q : Pred A q} (Q? : Decidable Q) (Q-resp-≈ : Q Respects _≈_)
         (P⊆Q : P ⊆ᵤ Q)
         where

  filter-⊂ : ∀ {v xs} → v ∈ xs → .(v ∉ᵤ P) → v ∈ᵤ Q → filter P? xs ⊂ filter Q? xs
  filter-⊂ {v} {x ∷ xs} (here v≈x) v∉P v∈Q with P? x | Q? x
  ... | yes x∈P | _       = ⊥-elim (v∉P (P-resp-≈ (sym v≈x) x∈P))
  ... | no  _   | no  x∉Q = contradiction (Q-resp-≈ v≈x v∈Q) x∉Q
  ... | no  _   | yes _   = x ∷ʳₛ′ filter⁺ P? Q? (λ a≈b → Q-resp-≈ a≈b ∘ P⊆Q) (⊆-refl {xs})
  filter-⊂ {v} {x ∷ xs} (there v∈xs) v∉P v∈Q with P? x | Q? x
  ... | yes x∈P | no  x∉Q = contradiction (P⊆Q x∈P) x∉Q
  ... | yes x∈P | yes x∈Q = refl ∷ₛ filter-⊂ v∈xs v∉P v∈Q
  ... | no  x∉P | yes x∈Q = x ∷ʳₛ′ filter⁺ P? Q? (λ a≈b → Q-resp-≈ a≈b ∘ P⊆Q) (⊆-refl {xs})
  ... | no  x∉P | no  x∉Q = filter-⊂ v∈xs v∉P v∈Q

length-mono-< : ∀ {xs ys} → xs ⊂ ys → length xs < length ys
length-mono-< {xs} {ys} ([]           , ¬[]≋[]) = contradiction [] ¬[]≋[] 
length-mono-< {xs} {ys} (x≈y ∷ xs⊆ys  , ¬xs≋ys) = s≤s (length-mono-< (xs⊆ys , ¬xs≋ys ∘ (x≈y ∷_)))
length-mono-< {xs} {ys} (y   ∷ʳ xs⊆ys , _)      = s≤s (length-mono-≤ xs⊆ys)
