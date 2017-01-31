open import Data.Nat using (ℕ; suc; zero)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.List using (map)
open import Data.List.Any as Any using (here; there)
open import Relation.Binary using (Setoid)
open import Relation.Binary.PropositionalEquality using (setoid; refl; cong; cong₂)

open import RoutingLib.Data.List using (allFin; combine)

module RoutingLib.Data.List.Any.PropositionalMembership where

  open Any.Membership-≡ public

  import RoutingLib.Data.List.Any.GenericMembership as GM

  ∈-map : ∀ {a b} {A : Set a} {B : Set b} {v xs}
          (f : A → B) → v ∈ xs → f v ∈ map f xs
  ∈-map {A = A} {B} f = GM.∈-map (setoid B) (setoid A) (cong f)

  ∈-combine : ∀ {a b} {A : Set a} {B : Set b} {u v xs ys}
              (f : A → A → B) → u ∈ xs → v ∈ ys → f u v ∈ combine f xs ys
  ∈-combine {A = A} {B} f = GM.∈-combine (setoid B) (setoid A) (cong₂ f)

  ∈-allFin : ∀ {m} n → n ∈ allFin m
  ∈-allFin fzero    = here refl
  ∈-allFin (fsuc n) = there (∈-map fsuc (∈-allFin n))
