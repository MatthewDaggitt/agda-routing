open import Data.List using (List; []; _∷_; map; _++_)
open import Data.List.Any using (here; there; any)
open import Data.List.All.Properties using (gmap; ¬Any⇒All¬; All¬⇒¬Any; tabulate⁺)
open import Data.List.Relation.Unary.Unique.Setoid.Properties
open import Data.List.Membership.Setoid.Properties
open import Data.List.Relation.Unary.Unique.Setoid as Uniqueness using (Unique)
open import Data.List.Relation.Unary.AllPairs using (AllPairs; []; _∷_)
import Data.List.Relation.Binary.Disjoint.Setoid as Disjoint
import Data.List.Relation.Unary.AllPairs.Properties as AllPairs
open import Data.Fin using (Fin) renaming (suc to fsuc)
open import Data.Fin.Properties using (suc-injective)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Function using (_∘_)
open import Relation.Binary using (DecSetoid; Setoid; Rel)
open import Relation.Nullary using (yes; no)

open import RoutingLib.Data.List
open import RoutingLib.Data.List.Membership.Setoid.Properties

module RoutingLib.Data.List.Relation.Unary.Uniqueness.Setoid.Properties where

  module _ {c ℓ} (DS : DecSetoid c ℓ) where

    open DecSetoid DS renaming (setoid to S)
    open import RoutingLib.Data.List.Membership.DecSetoid DS using (deduplicate)
    open import RoutingLib.Data.List.Membership.DecSetoid.Properties using (∈-deduplicate⁻)

    deduplicate!⁺ : ∀ xs → Unique S (deduplicate xs)
    deduplicate!⁺ [] = []
    deduplicate!⁺ (x ∷ xs) with any (x ≟_) xs
    ... | yes _    = deduplicate!⁺ xs
    ... | no  x∉xs = ¬Any⇒All¬ _ (x∉xs ∘ (∈-deduplicate⁻ DS)) ∷ deduplicate!⁺ xs


  module TripleSetoid {c₁ c₂ c₃ ℓ₁ ℓ₂ ℓ₃} (S₁ : Setoid c₁ ℓ₁) (S₂ : Setoid c₂ ℓ₂) (S₃ : Setoid c₃ ℓ₃) where

    open Setoid S₁ renaming (Carrier to A₁; _≈_ to _≈₁_; sym to sym₁; trans to trans₁)
    open Setoid S₂ renaming (Carrier to A₂; _≈_ to _≈₂_; sym to sym₂; trans to trans₂)
    open Setoid S₃ renaming (Carrier to A₃; _≈_ to _≈₃_)

    open Disjoint S₃ using (Disjoint)

    combine!⁺ : ∀ {xs ys} f → (∀ {w x y z} → f w y ≈₃ f x z → w ≈₁ x × y ≈₂ z) →
                Unique S₁ xs → Unique S₂ ys → Unique S₃ (combine f xs ys)
    combine!⁺ _ _ [] _ = []
    combine!⁺ {x ∷ xs} {ys} f f-inj (x∉xs ∷ xs!) ys! = ++⁺ S₃ (map⁺ S₂ S₃ (proj₂ ∘ f-inj) ys!) (combine!⁺ f f-inj xs! ys!) map#combine
      where
      map#combine : Disjoint (map (f x) ys) (combine f xs ys)
      map#combine (v∈map , v∈com) with ∈-map⁻ S₂ S₃ v∈map | combine-∈ S₁ S₂ S₃ f xs ys v∈com
      ... | (c , _ , v≈fxc) | (a , b , a∈xs , _ , v≈fab) = All¬⇒¬Any x∉xs (∈-resp-≈ S₁ (proj₁ (f-inj (trans (sym v≈fab) v≈fxc))) a∈xs)

  open TripleSetoid public
