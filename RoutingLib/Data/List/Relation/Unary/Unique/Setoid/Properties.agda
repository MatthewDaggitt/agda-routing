open import Data.List hiding (any)
open import Data.List.Properties using (filter-all)
open import Data.List.Relation.Unary.Any using (here; there; any)
open import Data.List.Relation.Unary.All.Properties using (all-filter; gmap; ¬Any⇒All¬; All¬⇒¬Any; tabulate⁺)
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
open import Relation.Nullary using (yes; no; ¬?)
open import Relation.Nullary.Negation using (contradiction)

open import RoutingLib.Data.List
open import RoutingLib.Data.List.Properties
open import RoutingLib.Data.List.Membership.Setoid.Properties

module RoutingLib.Data.List.Relation.Unary.Unique.Setoid.Properties where

private
  variable
    a ℓ : Level

module _ (DS : DecSetoid a ℓ) where

  open DecSetoid DS renaming (setoid to S)

  deduplicate⁺ : ∀ xs → Unique S (deduplicate _≟_ xs)
  deduplicate⁺ []       = []
  deduplicate⁺ (x ∷ xs) = all-filter (¬? ∘ (x ≟_)) (deduplicate _≟_ xs) ∷ (filter⁺ S (¬? ∘ (x ≟_)) (deduplicate⁺ xs))

module _ (S : Setoid a ℓ) where
  open Setoid S
  
  lookup-injective : ∀ {xs} → Unique S xs → Injective _≡_ _≈_ (lookup xs)
  lookup-injective (x∉xs ∷ xs!) {zero}  {zero}  eq = P.refl
  lookup-injective (x∉xs ∷ xs!) {zero}  {suc j} eq = contradiction (∈-resp-≈ S (sym eq) (∈-lookup S _ j)) (All¬⇒¬Any x∉xs)
  lookup-injective (x∉xs ∷ xs!) {suc i} {zero}  eq = contradiction (∈-resp-≈ S eq       (∈-lookup S _ i)) (All¬⇒¬Any x∉xs)
  lookup-injective (x∉xs ∷ xs!) {suc i} {suc j} eq = cong suc (lookup-injective xs! eq)
