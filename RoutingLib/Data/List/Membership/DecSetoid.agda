open import Relation.Binary using (DecSetoid; _Respects_; Decidable)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All; _∷_)
open import Data.List.Relation.Unary.Any using (any; here; there)
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Negation using (¬?)

module RoutingLib.Data.List.Membership.DecSetoid {c ℓ} (S : DecSetoid c ℓ) where

open import Data.List.Membership.DecSetoid S

_∉?_ : Decidable _∉_
x ∉? xs = ¬? (x ∈? xs)
