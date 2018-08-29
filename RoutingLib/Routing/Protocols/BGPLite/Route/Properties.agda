open import Data.Nat using (ℕ; _≟_; _<_)
open import Data.Nat.Properties using (<-cmp; <-trans; <-asym; <-irrefl)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; subst; cong; isEquivalence)
open import Relation.Binary.Lattice using (Minimum; Maximum)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Negation using (contradiction)

open import RoutingLib.Data.Path.Uncertified using ([]; length)
open import RoutingLib.Data.Path.Uncertified.Properties

open import RoutingLib.Routing.Protocols.BGPLite.Communities
open import RoutingLib.Routing.Protocols.BGPLite.Route

module RoutingLib.Routing.Protocols.BGPLite.Route.Properties where

--------------
-- Equality --
--------------



------------
-- Orders --
------------
