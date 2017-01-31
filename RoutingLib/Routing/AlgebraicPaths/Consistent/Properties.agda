open import Level using (_⊔_)
open import Data.Nat using (ℕ; suc; zero; _≤_; _<_; s≤s; z≤n)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Nullary using (¬_; yes; no)
open import Data.Product using (∄; ∃; _×_; _,_)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Fin.Properties using () renaming (_≟_ to _≟ᶠ_)
open import Data.List.Any using (here; there; module Membership)
open import Data.List using (List; []; _∷_; map)
open import Data.Maybe using (just; nothing; Eq)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary using (Decidable; Rel; IsDecEquivalence; Transitive)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; subst; inspect; [_]; cong) renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans)
open import Algebra.FunctionProperties using (Op₂; Idempotent; Associative; Commutative; RightIdentity; RightZero)

open import RoutingLib.Algebra.FunctionProperties using (Selective)
open import RoutingLib.Routing.Definitions
open import RoutingLib.Data.Graph using (Graph; _ᵉ∈ᵍ_; _ᵉ∈ᵍ?_)
open import RoutingLib.Data.Graph.SGPath hiding (weight)
open import RoutingLib.Data.Graph.SGPath.Properties
open import RoutingLib.Data.Graph.SGPath.Enumerate
open import RoutingLib.Data.Maybe.Properties using (just-injective)
open import RoutingLib.Data.List.All using (_∷_)
open import RoutingLib.Data.List.All.Properties using (forced-map)
open import RoutingLib.Data.List.All.Uniqueness using (Unique)
open import RoutingLib.Data.List.All.Uniqueness.Properties using (map!)
open import RoutingLib.Data.List.Any.GenericMembership using (∈-map; ∈-resp-≈)
open import RoutingLib.Data.List.Enumeration
open import RoutingLib.Routing.Algorithms.DistributedBellmanFord.ConvergenceConditions

module RoutingLib.Routing.AlgebraicPaths.Consistent.Properties
  {a b ℓ} (ra : RoutingAlgebra a b ℓ)
  (⊕-sel : Selective (RoutingAlgebra._≈_ ra) (RoutingAlgebra._⊕_ ra))
  {n : ℕ}
  (G : Graph (RoutingAlgebra.Step ra) n)
  where

  open RoutingAlgebra ra
  open import RoutingLib.Routing.AlgebraicPaths.Consistent ra ⊕-sel G
  open import RoutingLib.Algebra.Selectivity.Properties using () renaming (idem to sel⇨idem)
  open import RoutingLib.Algebra.Selectivity.NaturalOrders S _⊕_ ⊕-pres-≈ using (_≤ᵣ_; ≤ᵣ-trans; ≤ᵣ⇨≤ₗ; ≤ₗ⇨≤ᵣ)

  open Membership Cₛ using () renaming (_∈_ to _∈ᶜ_; ∈-resp-≈ to ∈ᶜ-resp-≈ₚ)


  abstract

    -------------------
    -- ⊕ᶜ properties --
    -------------------

    ⊕ᶜ-sel : Selective _≈ᶜ_ _⊕ᶜ_
    ⊕ᶜ-sel cnull          _              = inj₂ ≈ᶜ-refl
    ⊕ᶜ-sel (croute _ _ _) cnull          = inj₁ ≈ᶜ-refl
    ⊕ᶜ-sel (croute x p _) (croute y q _) with select x y
    ... | sel₁ _ _ = inj₁ ≈ᶜ-refl
    ... | sel₂ _ _ = inj₂ ≈ᶜ-refl
    ... | sel≈ _ _ with p ≤ₚ? q
    ...   | yes _ = inj₁ ≈ᶜ-refl
    ...   | no  _ = inj₂ ≈ᶜ-refl

    ⊕ᶜ-idem : Idempotent _≈ᶜ_ _⊕ᶜ_
    ⊕ᶜ-idem = sel⇨idem _≈ᶜ_ _⊕ᶜ_ ⊕ᶜ-sel

    ⊕ᶜ-comm : Commutative _≈_ _⊕_ → Commutative _≈ᶜ_ _⊕ᶜ_
    ⊕ᶜ-comm _    cnull          cnull          = ≈ᶜ-refl
    ⊕ᶜ-comm _    cnull          (croute _ _ _) = ≈ᶜ-refl
    ⊕ᶜ-comm _    (croute _ _ _) cnull          = ≈ᶜ-refl
    ⊕ᶜ-comm comm (croute x p _) (croute y q _) with select x y | select y x
    ... | sel₁ x⊕y≈x _     | sel₁ _     y⊕x≉x = contradiction (trans (comm y x) x⊕y≈x) y⊕x≉x
    ... | sel₁ _     _     | sel₂ _     _     = ≈ᶜ-refl
    ... | sel₁ _     x⊕y≉y | sel≈ y⊕x≈y _     = contradiction (trans (comm x y) y⊕x≈y) x⊕y≉y
    ... | sel₂ _ _         | sel₁ _     _     = ≈ᶜ-refl
    ... | sel₂ x⊕y≉x _     | sel₂ _     y⊕x≈x = contradiction (trans (comm x y) y⊕x≈x) x⊕y≉x
    ... | sel₂ x⊕y≉x _     | sel≈ _     y⊕x≈x = contradiction (trans (comm x y) y⊕x≈x) x⊕y≉x
    ... | sel≈ x⊕y≈x _     | sel₁ _     y⊕x≉x = contradiction (trans (comm y x) x⊕y≈x) y⊕x≉x
    ... | sel≈ _     x⊕y≈y | sel₂ y⊕x≉y _     = contradiction (trans (comm y x) x⊕y≈y) y⊕x≉y
    ... | sel≈ x⊕y≈x x⊕y≈y | sel≈ _     _     with p ≤ₚ? q | q ≤ₚ? p
    ...   | yes p≤q | yes q≤p = crouteEq (trans (sym x⊕y≈x) x⊕y≈y) (≤ₚ-antisym p≤q q≤p)
    ...   | yes _   | no  _   = ≈ᶜ-refl
    ...   | no  _   | yes _   = ≈ᶜ-refl
    ...   | no  p≰q | no  q≰p with ≤ₚ-total p q
    ...     | inj₁ p≤q = contradiction p≤q p≰q
    ...     | inj₂ q≤p = contradiction q≤p q≰p

    ⊕ᶜ-assoc : Commutative _≈_ _⊕_ → Associative _≈_ _⊕_ → Associative _≈ᶜ_ _⊕ᶜ_
    ⊕ᶜ-assoc comm assoc cnull          cnull          cnull          = ≈ᶜ-refl
    ⊕ᶜ-assoc comm assoc cnull          cnull          (croute _ _ _) = ≈ᶜ-refl
    ⊕ᶜ-assoc comm assoc cnull          (croute _ _ _) cnull          = ≈ᶜ-refl
    ⊕ᶜ-assoc comm assoc cnull          (croute _ _ _) (croute _ _ _) = ≈ᶜ-refl
    ⊕ᶜ-assoc comm assoc (croute _ _ _) cnull          cnull          = ≈ᶜ-refl
    ⊕ᶜ-assoc comm assoc (croute _ _ _) cnull          (croute _ _ _) = ≈ᶜ-refl
    ⊕ᶜ-assoc comm assoc (croute x p _) (croute y q _) cnull          with select x y
    ... | sel₁ _ _ = ≈ᶜ-refl
    ... | sel₂ _ _ = ≈ᶜ-refl
    ... | sel≈ _ _ with p ≤ₚ? q
    ...   | yes _ = ≈ᶜ-refl
    ...   | no  _ = ≈ᶜ-refl
    ⊕ᶜ-assoc comm assoc (croute x p x≈w[p]) (croute y q y≈w[q]) (croute z r z≈w[r]) = res
      where
      res : (croute x p x≈w[p] ⊕ᶜ croute y q y≈w[q]) ⊕ᶜ croute z r z≈w[r] ≈ᶜ croute x p x≈w[p] ⊕ᶜ (croute y q y≈w[q] ⊕ᶜ croute z r z≈w[r])
      res with select x y | select y z
      res | sel₁ _   _   | sel₁ _   _   with select x y | select x z
      res | sel₁ _   _   | sel₁ _   _   | sel₁ _   _   | sel₁ _   _   = ≈ᶜ-refl
      res | sel₁ x≤y _   | sel₁ _   z≰y | sel₁ _   _   | sel₂ _   z≤x = contradiction (≤ᵣ-trans assoc z≤x (≤ₗ⇨≤ᵣ comm x≤y)) z≰y
      res | sel₁ x≤y _   | sel₁ _   z≰y | sel₁ _   _   | sel≈ _   z≤x = contradiction (≤ᵣ-trans assoc z≤x (≤ₗ⇨≤ᵣ comm x≤y)) z≰y
      res | sel₁ x≤y _   | sel₁ _   _   | sel₂ x≰y _   | _            = contradiction x≤y x≰y
      res | sel₁ _   y≰x | sel₁ _   _   | sel≈ _   y≤x | _            = contradiction y≤x y≰x
      res | sel₁ _   _   | sel₂ _   _   = ≈ᶜ-refl
      res | sel₁ _   _   | sel≈ _   _   with q ≤ₚ? r
      res | sel₁ _   _   | sel≈ _   _   | yes _        with select x y | select x z
      res | sel₁ _   _   | sel≈ _   _   | yes _        | sel₁ _   _   | sel₁ _   _   = ≈ᶜ-refl
      res | sel₁ x≤y _   | sel≈ y≤z _   | yes _        | sel₁ _   _   | sel₂ x≰z _   = contradiction (≤ᵣ⇨≤ₗ comm (≤ᵣ-trans assoc (≤ₗ⇨≤ᵣ comm x≤y) (≤ₗ⇨≤ᵣ comm y≤z))) x≰z
      res | sel₁ _   y≰x | sel≈ y≤z _   | yes _        | sel₁ _   _   | sel≈ _   z≤x = contradiction (≤ᵣ-trans assoc (≤ₗ⇨≤ᵣ comm y≤z) z≤x) y≰x
      res | sel₁ x≤y _   | sel≈ _   _   | yes _        | sel₂ x≰y _   | _            = contradiction x≤y x≰y
      res | sel₁ _   y≰x | sel≈ _   _   | yes _        | sel≈ _   y≤x | _            = contradiction y≤x y≰x
      res | sel₁ _   _   | sel≈ _   _   | no  _        = ≈ᶜ-refl
      res | sel₂ _   _   | sel₁ _   _   with select x y | select y z
      res | sel₂ _   y≤x | sel₁ _   _   | sel₁ _   y≰x | _            = contradiction y≤x y≰x
      res | sel₂ _   _   | sel₁ _   _   | sel₂ _   _   | sel₁ _   _   = ≈ᶜ-refl
      res | sel₂ x≰y _   | sel₁ _   _   | sel≈ x≤y _   | _            = contradiction x≤y x≰y
      res | sel₂ _   _   | sel₁ y≤z _   | _            | sel₂ y≰z _   = contradiction y≤z y≰z
      res | sel₂ _   _   | sel₁ _   z≰y | _            | sel≈ _   z≤y = contradiction z≤y z≰y
      res | sel₂ _   _   | sel₂ _   _   with select x z | select y z
      res | sel₂ _   _   | sel₂ _   z≤y | _            | sel₁ _   z≰y = contradiction z≤y z≰y
      res | sel₂ x≰y _   | sel₂ _   z≤y | sel₁ x≤z _   | sel₂ _   _   = contradiction (≤ᵣ⇨≤ₗ comm (≤ᵣ-trans assoc (≤ₗ⇨≤ᵣ comm x≤z) z≤y)) x≰y
      res | sel₂ _   _   | sel₂ _   _   | sel₂ _   _   | sel₂ _   _   = ≈ᶜ-refl
      res | sel₂ x≰y _   | sel₂ _   z≤y | sel≈ x≤z _   | sel₂ _   _   = contradiction (≤ᵣ⇨≤ₗ comm (≤ᵣ-trans assoc (≤ₗ⇨≤ᵣ comm x≤z) z≤y)) x≰y
      res | sel₂ _   _   | sel₂ y≰z _   | _            | sel≈ y≤z _   = contradiction y≤z y≰z
      res | sel₂ _   _   | sel≈ _   _   with q ≤ₚ? r
      res | sel₂ _   _   | sel≈ _   _   | yes _        with select x y | select y z
      res | sel₂ _   y≤x | sel≈ _   _   | yes _        | sel₁ _   y≰x | _            = contradiction y≤x y≰x
      res | sel₂ _   _   | sel≈ _   z≤y | yes _        | _            | sel₁ _   z≰y = contradiction z≤y z≰y
      res | sel₂ _   _   | sel≈ y≤z _   | yes _        | _            | sel₂ y≰z _   = contradiction y≤z y≰z
      res | sel₂ _   _   | sel≈ _   _   | yes _        | sel₂ _   _   | sel≈ _   _   with q ≤ₚ? r
      res | sel₂ _   _   | sel≈ _   _   | yes _        | sel₂ _   _   | sel≈ _   _   | yes _        = ≈ᶜ-refl
      res | sel₂ _   _   | sel≈ _   _   | yes q≤r      | sel₂ _   _   | sel≈ _   _   | no  q≰r      = contradiction q≤r q≰r
      res | sel₂ x≰y _   | sel≈ _   _   | yes _        | sel≈ x≤y _   | _            = contradiction x≤y x≰y
      res | sel₂ _   _   | sel≈ _   _   | no  _        with select x z | select y z
      res | sel₂ _   _   | sel≈ _   z≤y | no  _        | _            | sel₁ _   z≰y = contradiction z≤y z≰y
      res | sel₂ _   _   | sel≈ y≤z _   | no  _        | _            | sel₂ y≰z _   = contradiction y≤z y≰z
      res | sel₂ x≰y _   | sel≈ _   z≤y | no  _        | sel₁ x≤z _   | sel≈ _   _   = contradiction (≤ᵣ⇨≤ₗ comm (≤ᵣ-trans assoc (≤ₗ⇨≤ᵣ comm x≤z) z≤y)) x≰y
      res | sel₂ _   _   | sel≈ _   _   | no  _        | sel₂ _   _   | sel≈ _   _   with q ≤ₚ? r
      res | sel₂ _   _   | sel≈ _   _   | no  q≰r      | sel₂ _   _   | sel≈ _   _   | yes q≤r      = contradiction q≤r q≰r
      res | sel₂ _   _   | sel≈ _   _   | no  _        | sel₂ _   _   | sel≈ _   _   | no  _        = ≈ᶜ-refl
      res | sel₂ x≰y _   | sel≈ _   z≤y | no  _        | sel≈ x≤z _   | sel≈ _   _   = contradiction (≤ᵣ⇨≤ₗ comm (≤ᵣ-trans assoc (≤ₗ⇨≤ᵣ comm x≤z) z≤y)) x≰y
      res | sel≈ _   _   | sel₁ _   _   with p ≤ₚ? q
      res | sel≈ _   _   | sel₁ _   _   | yes _        with select x y | select x z
      res | sel≈ _   y≤x | sel₁ _   _   | yes _        | sel₁ _   y≰x | _            = contradiction y≤x y≰x
      res | sel≈ x≤y _   | sel₁ _   _   | yes _        | sel₂ x≰y _   | _            = contradiction x≤y x≰y
      res | sel≈ _   _   | sel₁ _   _   | yes _        | sel≈ _   _   | sel₁ _   _   with p ≤ₚ? q
      res | sel≈ _   _   | sel₁ _   _   | yes _        | sel≈ _   _   | sel₁ _   _   | yes _         = ≈ᶜ-refl
      res | sel≈ _   _   | sel₁ _   _   | yes p≤q      | sel≈ _   _   | sel₁ _   _   | no  p≰q       = contradiction p≤q p≰q
      res | sel≈ x≤y _   | sel₁ _   z≰y | yes _        | sel≈ _   _   | sel₂ _   z≤x = contradiction (≤ᵣ-trans assoc z≤x (≤ₗ⇨≤ᵣ comm x≤y)) z≰y
      res | sel≈ x≤y _   | sel₁ _   z≰y | yes _        | sel≈ _   _   | sel≈ _   z≤x = contradiction (≤ᵣ-trans assoc z≤x (≤ₗ⇨≤ᵣ comm x≤y)) z≰y
      res | sel≈ _   _   | sel₁ _   _   | no  _        with select x y | select y z
      res | sel≈ _   y≤x | sel₁ _   _   | no  _        | sel₁ _   y≰x | _            = contradiction y≤x y≰x
      res | sel≈ x≤y _   | sel₁ _   _   | no  _        | sel₂ x≰y _   | _            = contradiction x≤y x≰y
      res | sel≈ _   _   | sel₁ _   _   | no  _        | sel≈ _   _   | sel₁ _   _   with p ≤ₚ? q
      res | sel≈ _   _   | sel₁ _   _   | no  p≰q      | sel≈ _   _   | sel₁ _   _   | yes p≤q      = contradiction p≤q p≰q
      res | sel≈ _   _   | sel₁ _   _   | no  _        | sel≈ _   _   | sel₁ _   _   | no  _        = ≈ᶜ-refl
      res | sel≈ _   _   | sel₁ x≤y _   | no  _        | _            | sel₂ x≰y _   = contradiction x≤y x≰y
      res | sel≈ _   _   | sel₁ _   y≰x | no  _        | _            | sel≈ _   y≤x = contradiction y≤x y≰x
      res | sel≈ _   _   | sel₂ _   _   with p ≤ₚ? q
      res | sel≈ _   _   | sel₂ _   _   | yes _        = ≈ᶜ-refl
      res | sel≈ _   _   | sel₂ _   _   | no  _        with select x z | select y z
      res | sel≈ _   _   | sel₂ _   z≤y | no  _        | _            | sel₁ _   z≰y = contradiction z≤y z≰y
      res | sel≈ _   y≤x | sel₂ y≰z _   | no  _        | sel₁ x≤z _   | sel₂ _   _   = contradiction (≤ᵣ⇨≤ₗ comm (≤ᵣ-trans assoc y≤x (≤ₗ⇨≤ᵣ comm x≤z))) y≰z
      res | sel≈ _   _   | sel₂ _   _   | no  _        | sel₂ _   _   | sel₂ _   _   = ≈ᶜ-refl
      res | sel≈ _   y≤x | sel₂ y≰z _   | no  _        | sel≈ x≤z _   | sel₂ _   _   = contradiction (≤ᵣ⇨≤ₗ comm (≤ᵣ-trans assoc y≤x (≤ₗ⇨≤ᵣ comm x≤z))) y≰z
      res | sel≈ _   _   | sel₂ y≰z _   | no  _        | _            | sel≈ y≤z _   = contradiction y≤z y≰z
      res | sel≈ _   _   | sel≈ _   _   with p ≤ₚ? q | q ≤ₚ? r
      res | sel≈ _   _   | sel≈ _   _   | yes _        | yes _        with select x y | select x z
      res | sel≈ _   y≤x | sel≈ _   _   | yes _        | yes _        | sel₁ _   y≰x | _            = contradiction y≤x y≰x
      res | sel≈ x≤y _   | sel≈ _   _   | yes _        | yes _        | sel₂ x≰y _   | _            = contradiction x≤y x≰y
      res | sel≈ _   y≤x | sel≈ _   z≤y | yes _        | yes _        | sel≈ _   _   | sel₁ _   z≰x = contradiction (≤ᵣ-trans assoc z≤y y≤x) z≰x
      res | sel≈ x≤y _   | sel≈ y≤z _   | yes _        | yes _        | sel≈ _   _   | sel₂ x≰z _   = contradiction (≤ᵣ⇨≤ₗ comm (≤ᵣ-trans assoc (≤ₗ⇨≤ᵣ comm x≤y) (≤ₗ⇨≤ᵣ comm y≤z))) x≰z
      res | sel≈ _   _   | sel≈ _   _   | yes _        | yes _        | sel≈ _   _   | sel≈ _   _   with p ≤ₚ? q | p ≤ₚ? r
      res | sel≈ _   _   | sel≈ _   _   | yes _        | yes _        | sel≈ _   _   | sel≈ _   _   | yes _       | yes _      = ≈ᶜ-refl
      res | sel≈ _   _   | sel≈ _   _   | yes p≤q      | yes q≤r      | sel≈ _   _   | sel≈ _   _   | yes _       | no  p≰r    = contradiction (≤ₚ-trans p≤q q≤r) p≰r
      res | sel≈ _   _   | sel≈ _   _   | yes p≤q      | yes _        | sel≈ _   _   | sel≈ _   _   | no  p≰q     | _          = contradiction p≤q p≰q
      res | sel≈ _   _   | sel≈ _   _   | yes _        | no  _        = ≈ᶜ-refl
      res | sel≈ _   _   | sel≈ _   _   | no  _        | yes _        with select x y | select y z
      res | sel≈ _   y≤x | sel≈ _   _   | no  _        | yes _        | sel₁ _   y≰x | _            = contradiction y≤x y≰x
      res | sel≈ x≤y _   | sel≈ _   _   | no  _        | yes _        | sel₂ x≰y _   | _            = contradiction x≤y x≰y
      res | sel≈ _   _   | sel≈ _   z≤y | no  _        | yes _        | _            | sel₁ _   z≰y = contradiction z≤y z≰y
      res | sel≈ _   _   | sel≈ y≤z _   | no  _        | yes _        | _            | sel₂ y≰z _   = contradiction y≤z y≰z
      res | sel≈ _   _   | sel≈ _   _   | no  _        | yes _        | sel≈ _   _   | sel≈ _   _   with p ≤ₚ? q | q ≤ₚ? r
      res | sel≈ _   _   | sel≈ _   _   | no  p≰q      | yes _        | sel≈ _   _   | sel≈ _   _   | yes p≤q     | _          = contradiction p≤q p≰q
      res | sel≈ _   _   | sel≈ _   _   | no  _        | yes q≤r      | sel≈ _   _   | sel≈ _   _   | _           | no  q≰r    = contradiction q≤r q≰r
      res | sel≈ _   _   | sel≈ _   _   | no  _        | yes _        | sel≈ _   _   | sel≈ _   _   | no  _       | yes _      = ≈ᶜ-refl
      res | sel≈ _   _   | sel≈ _   _   | no  _        | no  _        with select x z | select y z
      res | sel≈ _   _   | sel≈ _   z≤y | no  _        | no  _        | _            | sel₁ _   z≰y = contradiction z≤y z≰y
      res | sel≈ _   _   | sel≈ y≤z _   | no  _        | no  _        | _            | sel₂ y≰z _   = contradiction y≤z y≰z
      res | sel≈ _   y≤x | sel≈ _   z≤y | no  _        | no  _        | sel₁ _   z≰x | sel≈ _   _   = contradiction (≤ᵣ-trans assoc z≤y y≤x) z≰x
      res | sel≈ x≤y _   | sel≈ y≤z _   | no  _        | no  _        | sel₂ x≰z _   | sel≈ _   _   = contradiction (≤ᵣ⇨≤ₗ comm (≤ᵣ-trans assoc (≤ₗ⇨≤ᵣ comm x≤y) (≤ₗ⇨≤ᵣ comm y≤z))) x≰z
      res | sel≈ _   _   | sel≈ _   _   | no  _        | no  _        | sel≈ _   _   | sel≈ _   _   with p ≤ₚ? r | q ≤ₚ? r
      res | sel≈ _   _   | sel≈ _   _   | no  _        | no  q≰r      | sel≈ _   _   | sel≈ _   _   | _           | yes q≤r    = contradiction q≤r q≰r
      res | sel≈ _   _   | sel≈ _   _   | no  _        | no  _        | sel≈ _   _   | sel≈ _   _   | no  _       | no  _      = ≈ᶜ-refl
      res | sel≈ _   _   | sel≈ _   _   | no  _        | no  _        | sel≈ _   _   | sel≈ _   _   | yes _       | no  _      with ≤ₚ-total p q
      res | sel≈ _   _   | sel≈ _   _   | no  p≰q      | no  _        | sel≈ _   _   | sel≈ _   _   | yes _       | no  _      | inj₁ p≤q = contradiction p≤q p≰q
      res | sel≈ _   _   | sel≈ _   _   | no  p≰q      | no  q≰r      | sel≈ _   _   | sel≈ _   _   | yes p≤r     | no  _      | inj₂ q≤p = contradiction (≤ₚ-trans q≤p p≤r) q≰r


    ----------------------
    -- Properties of ▷ᶜ --
    ----------------------

    ⊕ᶜ-almost-strictly-absorbs-▷ᶜ : (∀ s r → (s ▷ r) ⊕ r ≈ r) → ∀ s {r} → r ≉ᶜ cnull → ((s ▷ᶜ r) ⊕ᶜ r ≈ᶜ r) × (r ≉ᶜ s ▷ᶜ r)
    ⊕ᶜ-almost-strictly-absorbs-▷ᶜ _   _       {cnull}           r≉cnull = contradiction ≈ᶜ-refl r≉cnull
    ⊕ᶜ-almost-strictly-absorbs-▷ᶜ abs (i , j) {croute x [] x≈1} _    with i ≟ᶠ j | (i , j) ᵉ∈ᵍ? G
    ... | yes _   | _       = ≈ᶜ-refl , λ()
    ... | no  _   | no  _   = ≈ᶜ-refl , λ()
    ... | no  i≢j | yes (v , b) with v ▷ x ≟ 0#
    ...   | yes _ = ≈ᶜ-refl , λ()
    ...   | no  _ with select (v ▷ x) x
    ...     | sel₁ _ vx⊕x≉x = contradiction (abs v x) vx⊕x≉x
    ...     | sel₂ _ _      = ≈ᶜ-refl , λ{(crouteEq x≈vx ())}
    ...     | sel≈ _ _      with [ i ∺ j ∣ i≢j ∣ (v , b) ] ≤ₚ? ([] {G = G})
    ...       | yes ()
    ...       | no  _ = ≈ᶜ-refl , λ{(crouteEq x≈vx ())}
    ⊕ᶜ-almost-strictly-absorbs-▷ᶜ abs (i , j) {croute x [ p ] x≈w[p]} _    with j ≟ᶠ source p | i ∉ₙₑₚ? p | (i , j) ᵉ∈ᵍ? G
    ... | no  _    | _       | _              = ≈ᶜ-refl , λ()
    ... | yes _    | no  _   | _              = ≈ᶜ-refl , λ()
    ... | yes _    | yes _   | no  _          = ≈ᶜ-refl , λ()
    ... | yes j≡p₀ | yes i∉p | yes (v , Gᵢⱼ≡v) with v ▷ x ≟ 0#
    ...   | yes _ = ≈ᶜ-refl , λ()
    ...   | no  _ with select (v ▷ x) x
    ...     | sel₁ _       vx⊕x≉x = contradiction (abs v x) vx⊕x≉x
    ...     | sel₂ vx⊕x≉vx _      = ≈ᶜ-refl , λ{(crouteEq _ [ p≈i∷p ]) → p≉i∷p p≈i∷p}
    ...     | sel≈ _       _      with [ i ∷ p ∣ i∉p ∣ (v , subst (λ j → G i j ≡ _) j≡p₀ Gᵢⱼ≡v) ] ≤ₚ? [ p ]
    ...       | yes i∷p≤p = contradiction i∷p≤p i∷p≰p
    ...       | no  i∷p≰p = ≈ᶜ-refl , λ{(crouteEq _ [ p≈i∷p ]) → p≉i∷p p≈i∷p}


    -------------------------------------
    -- Adjacency and identity matrices --
    -------------------------------------

    cnull-idᵣ-⊕ᶜ : RightIdentity _≈ᶜ_ cnull _⊕ᶜ_
    cnull-idᵣ-⊕ᶜ cnull           = ≈ᶜ-refl
    cnull-idᵣ-⊕ᶜ (croute x p x₁) = ≈ᶜ-refl

    cnull-anᵣ-▷ᶜ : ∀ e → e ▷ᶜ cnull ≈ᶜ cnull
    cnull-anᵣ-▷ᶜ _ = ≈ᶜ-refl

    1[]-anᵣ-⊕ᶜ : RightZero _≈_ 1# _⊕_ → RightZero _≈ᶜ_ (croute 1# [] refl) _⊕ᶜ_
    1[]-anᵣ-⊕ᶜ rz cnull = ≈ᶜ-refl
    1[]-anᵣ-⊕ᶜ rz (croute x p x≈wp) with select x 1#
    ... | sel₁ _ x⊕1≉1 = contradiction (rz x) x⊕1≉1
    ... | sel₂ _ _     = ≈ᶜ-refl
    ... | sel≈ _ _     with p | p ≤ₚ? []
    ...   | _     | no  _ = ≈ᶜ-refl
    ...   | []    | yes _ = crouteEq x≈wp []
    ...   | [ _ ] | yes ()





    -----------------
    -- Enumeration --
    -----------------

    pathToCRoute : SGPath G → CRoute
    pathToCRoute p = croute (weight p) p refl

    allCRoutes : List CRoute
    allCRoutes = cnull ∷ map pathToCRoute (allPaths G)

    pathToCRoute-¬cong : ∀ {p q} → p ≉ₚ q → ¬ (pathToCRoute p ≈ᶜ pathToCRoute q)
    pathToCRoute-¬cong p≉q (crouteEq _ p≈q) = p≉q p≈q

    pathToCRoute-cong : ∀ {p q} → p ≈ₚ q → pathToCRoute p ≈ᶜ pathToCRoute q
    pathToCRoute-cong p≈q = crouteEq (reflexive (weight-resp-≈ₚ _▷_ 1# p≈q)) p≈q

    allCRoutes! : Unique Cₛ allCRoutes
    allCRoutes! = forced-map (λ _ ()) (allPaths G) ∷ map! Cₛ (Pₛ G) pathToCRoute-¬cong (allPaths! G)

    ∈-allCRoutes : ∀ r → r ∈ᶜ allCRoutes
    ∈-allCRoutes cnull               = here cnullEq
    ∈-allCRoutes (croute x p x≈w[p]) = there (∈-resp-≈ Cₛ (∈-map Cₛ (Pₛ G) pathToCRoute-cong (∈-allPaths G p)) (crouteEq (sym x≈w[p]) ≈ₚ-refl))

    allCRoutes-isEnumeration : IsEnumeration Cₛ allCRoutes
    allCRoutes-isEnumeration = record {
        unique = allCRoutes!;
        complete = ∈-allCRoutes
      }


  ≈ᶜ-enumerable : Enumeration Cₛ
  ≈ᶜ-enumerable = record {
      list = allCRoutes ;
      isEnumeration = allCRoutes-isEnumeration
    }


  -----------
  -- Other --
  -----------

  convergenceConditions : ConvergenceConditionsWithPaths ra → ConvergenceConditions cra
  convergenceConditions ccwp = record {
       ⊕-assoc = ⊕ᶜ-assoc ⊕-comm ⊕-assoc;
       ⊕-sel = ⊕ᶜ-sel;
       ⊕-comm = ⊕ᶜ-comm ⊕-comm;
       ⊕-almost-strictly-absorbs-▷ = ⊕ᶜ-almost-strictly-absorbs-▷ᶜ ⊕-absorbs-▷;

       0#-idᵣ-⊕ = cnull-idᵣ-⊕ᶜ;
       0#-anᵣ-▷ = cnull-anᵣ-▷ᶜ;
       1#-anᵣ-⊕ = 1[]-anᵣ-⊕ᶜ 1#-anᵣ-⊕;

       routes-enumerable = ≈ᶜ-enumerable
    }
    where open ConvergenceConditionsWithPaths ccwp
