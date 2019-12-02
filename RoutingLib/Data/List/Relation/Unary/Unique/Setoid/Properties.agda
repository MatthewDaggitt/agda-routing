open import Data.List hiding (any)
open import Data.List.Any using (here; there; any)
open import Data.List.All.Properties using (gmap; ¬Any⇒All¬; All¬⇒¬Any; tabulate⁺)
open import Data.List.Relation.Unary.Unique.Setoid.Properties
open import Data.List.Membership.Setoid.Properties
open import Data.List.Relation.Unary.Unique.Setoid as Uniqueness using (Unique)
open import Data.List.Relation.Unary.AllPairs using (AllPairs; []; _∷_)
import Data.List.Relation.Binary.Disjoint.Setoid as Disjoint
import Data.List.Relation.Unary.AllPairs.Properties as AllPairs
open import Data.Fin using (Fin; zero; suc)
open import Data.Fin.Properties using (suc-injective)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Product.Relation.Binary.Pointwise.NonDependent using (_×ₛ_)
open import Level using (Level)
open import Function using (_∘_; Injective)
open import Function.Base using (id)
open import Relation.Binary using (DecSetoid; Setoid; Rel)
open import Relation.Binary.PropositionalEquality as P using (_≡_; cong)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Negation using (contradiction)

open import RoutingLib.Data.List
open import RoutingLib.Data.List.Properties
open import RoutingLib.Data.List.Membership.Setoid.Properties

module RoutingLib.Data.List.Relation.Unary.Unique.Setoid.Properties where

private
  variable
    a b c ℓ ℓ₁ ℓ₂ ℓ₃ : Level


module _ (DS : DecSetoid c ℓ) where

  open DecSetoid DS renaming (setoid to S)
  open import RoutingLib.Data.List.Membership.DecSetoid DS using (deduplicate)
  open import RoutingLib.Data.List.Membership.DecSetoid.Properties using (∈-deduplicate⁻)

  deduplicate⁺ : ∀ xs → Unique S (deduplicate xs)
  deduplicate⁺ [] = []
  deduplicate⁺ (x ∷ xs) with any (x ≟_) xs
  ... | yes _    = deduplicate⁺ xs
  ... | no  x∉xs = ¬Any⇒All¬ _ (x∉xs ∘ (∈-deduplicate⁻ DS)) ∷ deduplicate⁺ xs


module _ (S : Setoid a ℓ₁) (T : Setoid b ℓ₂) (U : Setoid c ℓ₃) where

  open Setoid S renaming (Carrier to A; _≈_ to _≈₁_; sym to sym₁; trans to trans₁)
  open Setoid T renaming (Carrier to B; _≈_ to _≈₂_; sym to sym₂; trans to trans₂)
  open Setoid U renaming (Carrier to C; _≈_ to _≈₃_)

  open Disjoint U using (Disjoint)

  combine⁺ : ∀ {xs ys} f → (∀ {w x y z} → f w y ≈₃ f x z → w ≈₁ x × y ≈₂ z) →
              Unique S xs → Unique T ys → Unique U (combine f xs ys)
  combine⁺ _ _ [] _ = []
  combine⁺ {x ∷ xs} {ys} f f-inj (x∉xs ∷ xs!) ys! = ++⁺ U (map⁺ T U (proj₂ ∘ f-inj) ys!) (combine⁺ f f-inj xs! ys!) map#combine
    where
    map#combine : Disjoint (map (f x) ys) (combine f xs ys)
    map#combine (v∈map , v∈com) with ∈-map⁻ T U v∈map | ∈-combine⁻ S T U f xs ys v∈com
    ... | (c , _ , v≈fxc) | (a , b , a∈xs , _ , v≈fab) = All¬⇒¬Any x∉xs (∈-resp-≈ S (proj₁ (f-inj (trans (sym v≈fab) v≈fxc))) a∈xs)

module _ (S : Setoid a ℓ₁) (T : Setoid b ℓ₂) where

  open Setoid S renaming (Carrier to A; _≈_ to _≈₁_; sym to sym₁; trans to trans₁)
  open Setoid T renaming (Carrier to B; _≈_ to _≈₂_; sym to sym₂; trans to trans₂)

  allPairs⁺ : ∀ {xs ys} → Unique S xs → Unique T ys → Unique (S ×ₛ T) (allPairs xs ys)
  allPairs⁺ = combine⁺ S T (S ×ₛ T) _,_ id


module _ (S : Setoid a ℓ₁) where
  open Setoid S
  
  lookup-injective : ∀ {xs} → Unique S xs → Injective _≡_ _≈_ (lookup xs)
  lookup-injective (x∉xs ∷ xs!) {zero}  {zero}  eq = P.refl
  lookup-injective (x∉xs ∷ xs!) {zero}  {suc j} eq = contradiction (∈-resp-≈ S (sym eq) (∈-lookup S _ j)) (All¬⇒¬Any x∉xs)
  lookup-injective (x∉xs ∷ xs!) {suc i} {zero}  eq = contradiction (∈-resp-≈ S eq       (∈-lookup S _ i)) (All¬⇒¬Any x∉xs)
  lookup-injective (x∉xs ∷ xs!) {suc i} {suc j} eq = cong suc (lookup-injective xs! eq)
