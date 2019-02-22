open import Algebra.FunctionProperties
open import Data.Nat using (ℕ; _≟_)
open import Data.Nat.Properties
  using (_<?_; <-trans; <-irrefl; <-asym; m+n≮n; m≤m+n; <⇒≱; ≤-refl; ≤-trans)
  renaming (<-cmp to compare)
open import Data.List using (List)
open import Data.Bool as 𝔹 using (Bool; _∧_; _∨_)
open import Data.Product using (_,_; _×_; proj₁; proj₂)
open import Data.Fin using (Fin; toℕ; fromℕ≤)
open import Data.Sum using (_⊎_; [_,_]′; inj₁; inj₂)
open import Function using (_∘_)
open import Relation.Unary using (Pred)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; subst; cong; cong₂; inspect; [_]; module ≡-Reasoning)
open import Relation.Binary using (Minimum; Maximum)
open import Level using () renaming (zero to ℓ₀; suc to lsuc)

import RoutingLib.Relation.Binary.Construct.NaturalOrder.Right as RightNaturalOrder
import RoutingLib.Algebra.Construct.NaturalChoice.Min.TotalOrder as NaturalChoice

open import RoutingLib.Data.Path.Uncertified using (inflate; deflate; length)
open import RoutingLib.Data.Path.UncertifiedI hiding (length)
open import RoutingLib.Data.Path.UncertifiedI.Properties

open import RoutingLib.Routing.Algebra
import RoutingLib.Routing.Algebra.Comparable as Comparable

open import RoutingLib.Routing.Protocols.PathVector.BGPLite
open import RoutingLib.Routing.Protocols.PathVector.BGPLite.Components.Route
open import RoutingLib.Routing.Protocols.PathVector.BGPLite.Components.Policy
  using (Policy; apply; reject; apply-result)
open import RoutingLib.Routing.Protocols.PathVector.BGPLite.Components.Communities

module RoutingLib.Routing.Protocols.PathVector.BGPLite.Properties where

open module Choice = NaturalChoice ≤ᵣ-totalOrder

--------------------------------------------------------------------------------
-- The algebra always converges (proved via a simulation with an equivalent but
-- better behaved routing algebra).

open import RoutingLib.Routing.Protocols.PathVector.BGPLite.Simulation
open import RoutingLib.Routing.VectorBased.Asynchronous.Convergence

δ-alwaysConvergent : AlwaysConvergent A
δ-alwaysConvergent = simulate Aₐₗₜ-simulates-A Aₐₗₜ-alwaysConvergent
