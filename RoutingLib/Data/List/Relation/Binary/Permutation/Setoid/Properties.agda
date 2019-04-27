{-# OPTIONS --allow-unsolved-metas #-}

open import Relation.Unary using (Decidable; Pred)
open import Relation.Binary
  using (Setoid; Rel; Reflexive; Transitive; Symmetric; IsEquivalence)
open import Data.List using ([]; _∷_; filter)

import RoutingLib.Data.List.Relation.Binary.Permutation.Setoid as PermutationSetoid

module RoutingLib.Data.List.Relation.Binary.Permutation.Setoid.Properties
  {b} {ℓ} {S : Setoid b ℓ}  where

open PermutationSetoid S
open Setoid S

-------------------

-- filter
↭-filter : ∀ {P : Pred Carrier ℓ} {xs ys}
           {P? : Decidable P} → xs ↭ ys → filter P? xs ↭ filter P? ys
↭-filter {P} {[]} {[]} {P?} xs↭ys = ↭-refl
↭-filter {P} {xs} {ys} {P?} xs↭ys = begin
  filter P? xs ↭⟨ {!!} ⟩
  filter P? ys ∎
  where open PermutationReasoning
