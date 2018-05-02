open import Level using (_⊔_)
open import Relation.Binary using (Setoid; Rel; Symmetric)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Nullary using (¬_)
open import Data.Empty using (⊥)
open import Data.List.Any using (Any)
open import Function using (_∘_)
open import Data.List using (List; []; _∷_; concat)
open import Data.List.Any.Properties using (++⁻)
open import Data.List.All using (All; []; _∷_; map)
open import Data.List.All.Properties using (¬Any⇒All¬)
open import Data.Product using (_×_; _,_; swap)
open import Data.Sum using (inj₁; inj₂)

import RoutingLib.Data.List.Membership.Setoid as Membership
open import RoutingLib.Data.List.All.Properties using (∈-All)

module RoutingLib.Data.List.Relation.Disjoint.Properties {c ℓ} (S : Setoid c ℓ) where

  open Setoid S renaming (Carrier to A)
  open import Data.List.Any.Membership S using (_∈_; _∉_)
  open import RoutingLib.Data.List.Relation.Disjoint S

  
  #-sym : Symmetric _#_
  #-sym xs#ys ∈both = xs#ys (swap ∈both)

  xs#[] : ∀ xs → xs # []
  xs#[] _ (_ , ())


  -- Operations on disjoint #
  
  #-concat : ∀ {vs xss} → All (vs #_) xss → vs # (concat xss)
  #-concat [] (_ , ())
  #-concat {xss = xs ∷ xss} (vs#xs ∷ vs#xss) (v∈vs , v∈xs++concatxss) with ++⁻ xs v∈xs++concatxss
  ... | inj₁ v∈xs  = vs#xs (v∈vs , v∈xs)
  ... | inj₂ v∈xss = #-concat vs#xss (v∈vs , v∈xss)
  
  -- Other
  #⇒AllAll≉ : ∀ {xs ys} → xs # ys → All (λ x → All (λ y → ¬ x ≈ y) ys) xs
  #⇒AllAll≉ xs#ys = map (¬Any⇒All¬ _) (∈-All S _ (λ v∈xs v∈ys → xs#ys (v∈xs , v∈ys)))
