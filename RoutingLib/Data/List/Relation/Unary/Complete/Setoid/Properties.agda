
module RoutingLib.Data.List.Relation.Unary.Complete.Setoid.Properties where

open import Data.Fin hiding (_≟_)
import Data.Fin.Properties as Fin
open import Data.List
open import Data.List.Membership.Setoid
open import Data.List.Membership.Setoid.Properties
open import Data.List.Membership.Propositional.Properties using (∈-allFin)
open import Data.List.Relation.Unary.Any using (index)
open import Data.List.Relation.Unary.Any.Properties using (lookup-index)
open import Data.Sum using (inj₁; inj₂)
open import Data.Sum.Relation.Binary.Pointwise using (_⊎ₛ_; inj₁; inj₂)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Product.Relation.Binary.Pointwise.NonDependent using (_×ₛ_)
open import Function
open import Level
open import Relation.Binary
open import Relation.Binary.PropositionalEquality using (_≡_)

open import RoutingLib.Data.List
open import RoutingLib.Data.List.Membership.Setoid.Properties
open import RoutingLib.Data.List.Relation.Unary.Complete.Setoid

private
  variable
    a b ℓ₁ ℓ₂ : Level
    A : Set a
    B : Set b

module _ (S : Setoid a ℓ₁) (T : Setoid b ℓ₂) where

  open Setoid S using () renaming (_≈_ to _≈₁_)
  open Setoid T using () renaming (_≈_ to _≈₂_)
  
  cartesianProduct⁺ : ∀ {xs ys} → Complete S xs → Complete T ys → Complete (S ×ₛ T) (cartesianProduct xs ys)
  cartesianProduct⁺ _∈xs _∈ys x = ∈-cartesianProduct⁺ S T ((proj₁ x) ∈xs) ((proj₂ x) ∈ys)

  map⁺ : ∀ {f xs} → Complete S xs → IsSurjection _≈₁_ _≈₂_ f → Complete T (map f xs)
  map⁺ _∈xs surj y with IsSurjection.surjective surj y
  ... | (x , fx≈y) = ∈-resp-≈ T fx≈y (∈-map⁺ S T (IsSurjection.cong surj) (x ∈xs))

module _ (S : Setoid a ℓ₁) (T : Setoid b ℓ₂) where

  ++⁺ : ∀ {xs ys} → Complete S xs → Complete T ys →
        Complete (S ⊎ₛ T) (map inj₁ xs ++ map inj₂ ys)
  ++⁺ _∈xs _ (inj₁ x) = ∈-++⁺ˡ (S ⊎ₛ T)   (∈-map⁺ S (S ⊎ₛ T) inj₁ (x ∈xs))
  ++⁺ _ _∈ys (inj₂ y) = ∈-++⁺ʳ (S ⊎ₛ T) _ (∈-map⁺ T (S ⊎ₛ T) inj₂ (y ∈ys))

module _ (S? : DecSetoid a ℓ₁) where
  open DecSetoid S? renaming (setoid to S)
  
  deduplicate⁺ : ∀ {xs} → Complete S xs → Complete S (deduplicate _≟_ xs)
  deduplicate⁺ complete = ∈-deduplicate⁺ S _≟_ (λ y≈z x≈z → trans x≈z (sym y≈z)) ∘ complete
  
module _ (S : Setoid a ℓ₁) where
  open Setoid S
  
  lookup-surjective : ∀ {xs} → Complete S xs → Surjective {A = Fin (length xs)} _≡_ _≈_ (lookup xs)
  lookup-surjective _∈xs y = index (y ∈xs) , sym (lookup-index (y ∈xs))

allFin⁺ : ∀ n → Complete (Fin.≡-setoid n) (allFin n)
allFin⁺ n = ∈-allFin
