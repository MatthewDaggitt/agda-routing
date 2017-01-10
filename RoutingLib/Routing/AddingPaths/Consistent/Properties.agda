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
open import RoutingLib.Data.Graph.EGPath hiding (weight)
open import RoutingLib.Data.Graph.EGPath.Properties
open import RoutingLib.Data.Maybe.Properties using (just-injective)
open import RoutingLib.Data.List.All using (_∷_)
open import RoutingLib.Data.List.All.Properties using (forced-map)
open import RoutingLib.Data.List.All.Uniqueness using (Unique)
open import RoutingLib.Data.List.All.Uniqueness.Properties using (map!)
open import RoutingLib.Data.List.Any.GenericMembership using (∈-map; ∈-resp-≈)
open import RoutingLib.Data.List.Enumeration


module RoutingLib.Routing.AddingPaths.Consistent.Properties
  {a b ℓ} (ra : RoutingAlgebra a b ℓ) 
  (⊕-sel : Selective (RoutingAlgebra._≈_ ra) (RoutingAlgebra._⊕_ ra))
  (one : (RoutingAlgebra.Route ra))
  {n : ℕ}
  (G : Graph (RoutingAlgebra.Step ra) n)
  where

  open RoutingAlgebra ra
  open import RoutingLib.Routing.AddingPaths.Consistent ra ⊕-sel one G
  open import RoutingLib.Algebra.Selectivity.Properties using () renaming (idem to sel⇨idem)
  open import RoutingLib.Algebra.Selectivity.NaturalOrders ≈-setoid _⊕_ ⊕-pres-≈ using (_≤ᵣ_; ≤ᵣ-trans; ≤ᵣ⇨≤ₗ; ≤ₗ⇨≤ᵣ)

  open Membership ≈ᶜ-setoid using () renaming (_∈_ to _∈ᶜ_; ∈-resp-≈ to ∈ᶜ-resp-≈ₚ)

  open import RoutingLib.Routing.Algorithms.DistributedBellmanFord crp
  open import RoutingLib.Routing.Algorithms.DistributedBellmanFord.Properties crp
  
  open import Relation.Binary.EqReasoning ≈ᶜ-setoid
  

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
    ... | sel≈ _ _ with p ≤ₗₚ? q
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
    ... | sel≈ x⊕y≈x x⊕y≈y | sel≈ _     _     with p ≤ₗₚ? q | q ≤ₗₚ? p
    ...   | yes p≤q | yes q≤p = crouteEq (trans (sym x⊕y≈x) x⊕y≈y) (≤ₗₚ-antisym p≤q q≤p)
    ...   | yes _   | no  _   = ≈ᶜ-refl
    ...   | no  _   | yes _   = ≈ᶜ-refl
    ...   | no  p≰q | no  q≰p with ≤ₗₚ-total p q
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
    ... | sel≈ _ _ with p ≤ₗₚ? q
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
      res | sel₁ _   _   | sel≈ _   _   with q ≤ₗₚ? r
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
      res | sel₂ _   _   | sel≈ _   _   with q ≤ₗₚ? r
      res | sel₂ _   _   | sel≈ _   _   | yes _        with select x y | select y z
      res | sel₂ _   y≤x | sel≈ _   _   | yes _        | sel₁ _   y≰x | _            = contradiction y≤x y≰x
      res | sel₂ _   _   | sel≈ _   z≤y | yes _        | _            | sel₁ _   z≰y = contradiction z≤y z≰y
      res | sel₂ _   _   | sel≈ y≤z _   | yes _        | _            | sel₂ y≰z _   = contradiction y≤z y≰z
      res | sel₂ _   _   | sel≈ _   _   | yes _        | sel₂ _   _   | sel≈ _   _   with q ≤ₗₚ? r
      res | sel₂ _   _   | sel≈ _   _   | yes _        | sel₂ _   _   | sel≈ _   _   | yes _        = ≈ᶜ-refl
      res | sel₂ _   _   | sel≈ _   _   | yes q≤r      | sel₂ _   _   | sel≈ _   _   | no  q≰r      = contradiction q≤r q≰r
      res | sel₂ x≰y _   | sel≈ _   _   | yes _        | sel≈ x≤y _   | _            = contradiction x≤y x≰y
      res | sel₂ _   _   | sel≈ _   _   | no  _        with select x z | select y z
      res | sel₂ _   _   | sel≈ _   z≤y | no  _        | _            | sel₁ _   z≰y = contradiction z≤y z≰y
      res | sel₂ _   _   | sel≈ y≤z _   | no  _        | _            | sel₂ y≰z _   = contradiction y≤z y≰z
      res | sel₂ x≰y _   | sel≈ _   z≤y | no  _        | sel₁ x≤z _   | sel≈ _   _   = contradiction (≤ᵣ⇨≤ₗ comm (≤ᵣ-trans assoc (≤ₗ⇨≤ᵣ comm x≤z) z≤y)) x≰y
      res | sel₂ _   _   | sel≈ _   _   | no  _        | sel₂ _   _   | sel≈ _   _   with q ≤ₗₚ? r
      res | sel₂ _   _   | sel≈ _   _   | no  q≰r      | sel₂ _   _   | sel≈ _   _   | yes q≤r      = contradiction q≤r q≰r
      res | sel₂ _   _   | sel≈ _   _   | no  _        | sel₂ _   _   | sel≈ _   _   | no  _        = ≈ᶜ-refl
      res | sel₂ x≰y _   | sel≈ _   z≤y | no  _        | sel≈ x≤z _   | sel≈ _   _   = contradiction (≤ᵣ⇨≤ₗ comm (≤ᵣ-trans assoc (≤ₗ⇨≤ᵣ comm x≤z) z≤y)) x≰y
      res | sel≈ _   _   | sel₁ _   _   with p ≤ₗₚ? q
      res | sel≈ _   _   | sel₁ _   _   | yes _        with select x y | select x z
      res | sel≈ _   y≤x | sel₁ _   _   | yes _        | sel₁ _   y≰x | _            = contradiction y≤x y≰x  
      res | sel≈ x≤y _   | sel₁ _   _   | yes _        | sel₂ x≰y _   | _            = contradiction x≤y x≰y
      res | sel≈ _   _   | sel₁ _   _   | yes _        | sel≈ _   _   | sel₁ _   _   with p ≤ₗₚ? q 
      res | sel≈ _   _   | sel₁ _   _   | yes _        | sel≈ _   _   | sel₁ _   _   | yes _         = ≈ᶜ-refl
      res | sel≈ _   _   | sel₁ _   _   | yes p≤q      | sel≈ _   _   | sel₁ _   _   | no  p≰q       = contradiction p≤q p≰q
      res | sel≈ x≤y _   | sel₁ _   z≰y | yes _        | sel≈ _   _   | sel₂ _   z≤x = contradiction (≤ᵣ-trans assoc z≤x (≤ₗ⇨≤ᵣ comm x≤y)) z≰y 
      res | sel≈ x≤y _   | sel₁ _   z≰y | yes _        | sel≈ _   _   | sel≈ _   z≤x = contradiction (≤ᵣ-trans assoc z≤x (≤ₗ⇨≤ᵣ comm x≤y)) z≰y  
      res | sel≈ _   _   | sel₁ _   _   | no  _        with select x y | select y z
      res | sel≈ _   y≤x | sel₁ _   _   | no  _        | sel₁ _   y≰x | _            = contradiction y≤x y≰x
      res | sel≈ x≤y _   | sel₁ _   _   | no  _        | sel₂ x≰y _   | _            = contradiction x≤y x≰y
      res | sel≈ _   _   | sel₁ _   _   | no  _        | sel≈ _   _   | sel₁ _   _   with p ≤ₗₚ? q
      res | sel≈ _   _   | sel₁ _   _   | no  p≰q      | sel≈ _   _   | sel₁ _   _   | yes p≤q      = contradiction p≤q p≰q
      res | sel≈ _   _   | sel₁ _   _   | no  _        | sel≈ _   _   | sel₁ _   _   | no  _        = ≈ᶜ-refl
      res | sel≈ _   _   | sel₁ x≤y _   | no  _        | _            | sel₂ x≰y _   = contradiction x≤y x≰y
      res | sel≈ _   _   | sel₁ _   y≰x | no  _        | _            | sel≈ _   y≤x = contradiction y≤x y≰x
      res | sel≈ _   _   | sel₂ _   _   with p ≤ₗₚ? q
      res | sel≈ _   _   | sel₂ _   _   | yes _        = ≈ᶜ-refl
      res | sel≈ _   _   | sel₂ _   _   | no  _        with select x z | select y z 
      res | sel≈ _   _   | sel₂ _   z≤y | no  _        | _            | sel₁ _   z≰y = contradiction z≤y z≰y
      res | sel≈ _   y≤x | sel₂ y≰z _   | no  _        | sel₁ x≤z _   | sel₂ _   _   = contradiction (≤ᵣ⇨≤ₗ comm (≤ᵣ-trans assoc y≤x (≤ₗ⇨≤ᵣ comm x≤z))) y≰z
      res | sel≈ _   _   | sel₂ _   _   | no  _        | sel₂ _   _   | sel₂ _   _   = ≈ᶜ-refl
      res | sel≈ _   y≤x | sel₂ y≰z _   | no  _        | sel≈ x≤z _   | sel₂ _   _   = contradiction (≤ᵣ⇨≤ₗ comm (≤ᵣ-trans assoc y≤x (≤ₗ⇨≤ᵣ comm x≤z))) y≰z
      res | sel≈ _   _   | sel₂ y≰z _   | no  _        | _            | sel≈ y≤z _   = contradiction y≤z y≰z
      res | sel≈ _   _   | sel≈ _   _   with p ≤ₗₚ? q | q ≤ₗₚ? r
      res | sel≈ _   _   | sel≈ _   _   | yes _        | yes _        with select x y | select x z 
      res | sel≈ _   y≤x | sel≈ _   _   | yes _        | yes _        | sel₁ _   y≰x | _            = contradiction y≤x y≰x
      res | sel≈ x≤y _   | sel≈ _   _   | yes _        | yes _        | sel₂ x≰y _   | _            = contradiction x≤y x≰y
      res | sel≈ _   y≤x | sel≈ _   z≤y | yes _        | yes _        | sel≈ _   _   | sel₁ _   z≰x = contradiction (≤ᵣ-trans assoc z≤y y≤x) z≰x
      res | sel≈ x≤y _   | sel≈ y≤z _   | yes _        | yes _        | sel≈ _   _   | sel₂ x≰z _   = contradiction (≤ᵣ⇨≤ₗ comm (≤ᵣ-trans assoc (≤ₗ⇨≤ᵣ comm x≤y) (≤ₗ⇨≤ᵣ comm y≤z))) x≰z
      res | sel≈ _   _   | sel≈ _   _   | yes _        | yes _        | sel≈ _   _   | sel≈ _   _   with p ≤ₗₚ? q | p ≤ₗₚ? r
      res | sel≈ _   _   | sel≈ _   _   | yes _        | yes _        | sel≈ _   _   | sel≈ _   _   | yes _       | yes _      = ≈ᶜ-refl
      res | sel≈ _   _   | sel≈ _   _   | yes p≤q      | yes q≤r      | sel≈ _   _   | sel≈ _   _   | yes _       | no  p≰r    = contradiction (≤ₗₚ-trans p≤q q≤r) p≰r
      res | sel≈ _   _   | sel≈ _   _   | yes p≤q      | yes _        | sel≈ _   _   | sel≈ _   _   | no  p≰q     | _          = contradiction p≤q p≰q
      res | sel≈ _   _   | sel≈ _   _   | yes _        | no  _        = ≈ᶜ-refl
      res | sel≈ _   _   | sel≈ _   _   | no  _        | yes _        with select x y | select y z
      res | sel≈ _   y≤x | sel≈ _   _   | no  _        | yes _        | sel₁ _   y≰x | _            = contradiction y≤x y≰x
      res | sel≈ x≤y _   | sel≈ _   _   | no  _        | yes _        | sel₂ x≰y _   | _            = contradiction x≤y x≰y
      res | sel≈ _   _   | sel≈ _   z≤y | no  _        | yes _        | _            | sel₁ _   z≰y = contradiction z≤y z≰y
      res | sel≈ _   _   | sel≈ y≤z _   | no  _        | yes _        | _            | sel₂ y≰z _   = contradiction y≤z y≰z
      res | sel≈ _   _   | sel≈ _   _   | no  _        | yes _        | sel≈ _   _   | sel≈ _   _   with p ≤ₗₚ? q | q ≤ₗₚ? r 
      res | sel≈ _   _   | sel≈ _   _   | no  p≰q      | yes _        | sel≈ _   _   | sel≈ _   _   | yes p≤q     | _          = contradiction p≤q p≰q
      res | sel≈ _   _   | sel≈ _   _   | no  _        | yes q≤r      | sel≈ _   _   | sel≈ _   _   | _           | no  q≰r    = contradiction q≤r q≰r
      res | sel≈ _   _   | sel≈ _   _   | no  _        | yes _        | sel≈ _   _   | sel≈ _   _   | no  _       | yes _      = ≈ᶜ-refl
      res | sel≈ _   _   | sel≈ _   _   | no  _        | no  _        with select x z | select y z
      res | sel≈ _   _   | sel≈ _   z≤y | no  _        | no  _        | _            | sel₁ _   z≰y = contradiction z≤y z≰y
      res | sel≈ _   _   | sel≈ y≤z _   | no  _        | no  _        | _            | sel₂ y≰z _   = contradiction y≤z y≰z
      res | sel≈ _   y≤x | sel≈ _   z≤y | no  _        | no  _        | sel₁ _   z≰x | sel≈ _   _   = contradiction (≤ᵣ-trans assoc z≤y y≤x) z≰x
      res | sel≈ x≤y _   | sel≈ y≤z _   | no  _        | no  _        | sel₂ x≰z _   | sel≈ _   _   = contradiction (≤ᵣ⇨≤ₗ comm (≤ᵣ-trans assoc (≤ₗ⇨≤ᵣ comm x≤y) (≤ₗ⇨≤ᵣ comm y≤z))) x≰z
      res | sel≈ _   _   | sel≈ _   _   | no  _        | no  _        | sel≈ _   _   | sel≈ _   _   with p ≤ₗₚ? r | q ≤ₗₚ? r
      res | sel≈ _   _   | sel≈ _   _   | no  _        | no  q≰r      | sel≈ _   _   | sel≈ _   _   | _           | yes q≤r    = contradiction q≤r q≰r
      res | sel≈ _   _   | sel≈ _   _   | no  _        | no  _        | sel≈ _   _   | sel≈ _   _   | no  _       | no  _      = ≈ᶜ-refl
      res | sel≈ _   _   | sel≈ _   _   | no  _        | no  _        | sel≈ _   _   | sel≈ _   _   | yes _       | no  _      with ≤ₗₚ-total p q
      res | sel≈ _   _   | sel≈ _   _   | no  p≰q      | no  _        | sel≈ _   _   | sel≈ _   _   | yes _       | no  _      | inj₁ p≤q = contradiction p≤q p≰q
      res | sel≈ _   _   | sel≈ _   _   | no  p≰q      | no  q≰r      | sel≈ _   _   | sel≈ _   _   | yes p≤r     | no  _      | inj₂ q≤p = contradiction (≤ₗₚ-trans q≤p p≤r) q≰r
      

    -------------------------------------
    -- Adjacency and identity matrices --
    -------------------------------------

    Iᶜᵢⱼ≡cnull : ∀ {i j} → j ≢ i → Iᶜ i j ≡ cnull
    Iᶜᵢⱼ≡cnull {i} {j} j≢i with j ≟ᶠ i
    ... | yes j≡i = contradiction j≡i j≢i
    ... | no  _   = ≡-refl

    Iᶜᵢᵢ≡one[i] : ∀ i → Iᶜ i i ≡ croute one [ i ] refl
    Iᶜᵢᵢ≡one[i] i with i ≟ᶠ i 
    ... | no  i≢i = contradiction ≡-refl i≢i
    ... | yes i≡i = ≡-refl

    cnull-idᵣ-⊕ᶜ : RightIdentity _≈ᶜ_ cnull _⊕ᶜ_
    cnull-idᵣ-⊕ᶜ cnull = cnullEq
    cnull-idᵣ-⊕ᶜ (croute _ _ _) = crouteEq refl ≈ₚ-refl

    cnull-anᵣ-▷ᶜ : ∀ e → e ▷ᶜ cnull ≈ᶜ cnull
    cnull-anᵣ-▷ᶜ cnone = ≈ᶜ-refl
    cnull-anᵣ-▷ᶜ (cedge _) = ≈ᶜ-refl

    Iᶜᵢᵢ-almost-anᵣ-⊕ᶜ : RightZero _≈_ one _⊕_  → ∀ l s r → (s ▷ᶜ r) ⊕ᶜ Iᶜ l l ≈ᶜ Iᶜ l l
    Iᶜᵢᵢ-almost-anᵣ-⊕ᶜ _ _ cnone     _     = ≈ᶜ-refl
    Iᶜᵢᵢ-almost-anᵣ-⊕ᶜ _ _ (cedge _) cnull = ≈ᶜ-refl
    Iᶜᵢᵢ-almost-anᵣ-⊕ᶜ an l (cedge (i , j , e)) (croute x p x≈w[p]) with j ≟ᶠ source p | i ∉? p | (i , j) ᵉ∈ᵍ? G
    ... | no  _ | _     | _     = ≈ᶜ-refl
    ... | yes _ | no  _ | _     = ≈ᶜ-refl
    ... | yes _ | yes _ | no  _ = ≈ᶜ-refl
    ... | yes _ | yes _ | yes (v , b) rewrite Iᶜᵢᵢ≡one[i] l with select (v ▷ x) one
    ...   | sel₁ _ vx⊕1≉1 = contradiction (an (v ▷ x)) vx⊕1≉1
    ...   | sel₂ _ _      = ≈ᶜ-refl
    ...   | sel≈ _ _      = ≈ᶜ-refl

    Aᵢⱼ▷cnull≡cnull : ∀ i j → Aᶜ i j ▷ᶜ cnull ≡ cnull
    Aᵢⱼ▷cnull≡cnull i j with G i j
    ... | nothing = ≡-refl
    ... | just _  = ≡-refl


    ----------------------
    -- Properties of ▷ᶜ --
    ----------------------

    ⊕ᶜ-almost-strictly-absorbs-▷ᶜ : (∀ s r → (s ▷ r) ⊕ r ≈ r) → ∀ s {r} → r ≉ᶜ cnull → ((s ▷ᶜ r) ⊕ᶜ r ≈ᶜ r) × (r ≉ᶜ s ▷ᶜ r)
    ⊕ᶜ-almost-strictly-absorbs-▷ᶜ _   _                   {cnull}             r≉cnull = contradiction ≈ᶜ-refl r≉cnull
    ⊕ᶜ-almost-strictly-absorbs-▷ᶜ _   cnone               {croute _ _ _}      _    = ≈ᶜ-refl , λ()
    ⊕ᶜ-almost-strictly-absorbs-▷ᶜ abs (cedge (i , j , e)) {croute x p x≈w[p]} _    with j ≟ᶠ source p | i ∉? p | (i , j) ᵉ∈ᵍ? G
    ... | no  _    | _       | _              = ≈ᶜ-refl , λ()
    ... | yes _    | no  _   | _              = ≈ᶜ-refl , λ()
    ... | yes _    | yes _   | no  _          = ≈ᶜ-refl , λ()
    ... | yes j≡p₀ | yes i∉p | yes (v , Gᵢⱼ≡v) with select (v ▷ x) x
    ...   | sel₁ _       vx⊕x≉x = contradiction (abs v x) vx⊕x≉x
    ...   | sel₂ vx⊕x≉vx _      = ≈ᶜ-refl , λ{(crouteEq x≈vx _) → vx⊕x≉vx (trans (⊕-pres-≈ refl x≈vx) (sel⇨idem _≈_ _⊕_ ⊕-sel (v ▷ x)))}
    ...   | sel≈ _       _      with i ∷ p ∣ i∉p ∣ (v , subst (λ w → G i w ≡ cedge v) j≡p₀ Gᵢⱼ≡v) ≤ₗₚ? p
    ...     | yes (i∷p≤ₗp , _) = contradiction i∷p≤ₗp (i∷p≰ₗp {i∉p = i∉p} (v , subst (λ w → G i w ≡ cedge v) j≡p₀ Gᵢⱼ≡v))
    ...     | no  i∷p≰p        = ≈ᶜ-refl , (λ{(crouteEq _ p≈i∷p) → p≉i∷p ((v , subst (λ w → G i w ≡ cedge v) j≡p₀ Gᵢⱼ≡v)) p≈i∷p})



    -----------------
    -- Enumeration --
    -----------------

    pathToCRoute : EGPath G → CRoute
    pathToCRoute p = croute (weight p) p refl
 
    allCRoutes : List CRoute
    allCRoutes = cnull ∷ map pathToCRoute (allPaths G)

    pathToCRoute-¬cong : ∀ {p q} → p ≉ₚ q → ¬ (pathToCRoute p ≈ᶜ pathToCRoute q)
    pathToCRoute-¬cong p≉q (crouteEq _ p≈q) = p≉q p≈q

    pathToCRoute-cong : ∀ {p q} → p ≈ₚ q → pathToCRoute p ≈ᶜ pathToCRoute q
    pathToCRoute-cong p≈q = crouteEq (reflexive (weight-resp-≈ₚ _▷_ one p≈q)) p≈q

    allCRoutes-unique : Unique ≈ᶜ-setoid allCRoutes
    allCRoutes-unique = forced-map (λ _ ()) (allPaths G) ∷ (map! ≈ₚ-setoid ≈ᶜ-setoid pathToCRoute-¬cong allPaths-unique)

    allCRoutes-complete : ∀ r → r ∈ᶜ allCRoutes
    allCRoutes-complete cnull               = here cnullEq
    allCRoutes-complete (croute x p x≈w[p]) = ∈-resp-≈ ≈ᶜ-setoid (there (∈-map ≈ₚ-setoid ≈ᶜ-setoid pathToCRoute-cong (allPaths-complete p))) (crouteEq (sym x≈w[p]) ≈ₚ-refl)

    allCRoutes-isEnumeration : IsEnumeration ≈ᶜ-setoid allCRoutes
    allCRoutes-isEnumeration = record { 
        unique = allCRoutes-unique; 
        complete = allCRoutes-complete
      }


  ≈ᶜ-enumerable : Enumeration ≈ᶜ-setoid
  ≈ᶜ-enumerable = record { 
      list = allCRoutes ; 
      isEnumeration = allCRoutes-isEnumeration 
    }


  -----------
  -- Other --
  -----------

  ▷ᶜ-success : ∀ {x p} x≈w[p] {i j v} v▷x≈v▷w[p] i∉p → j ≡ source p → (Gᵢⱼ≡v : G i (source p) ≡ just v) → Aᶜ i j ▷ᶜ (croute x p x≈w[p]) ≈ᶜ croute (v ▷ x) (i ∷ p ∣ i∉p ∣ (v , Gᵢⱼ≡v)) v▷x≈v▷w[p]
  ▷ᶜ-success {x} {p} x≈w[p] {i} {j} {v} v▷x≈v▷w[p] i∉p j≡p₀ Gᵢⱼ≡v with G i j | inspect (G i) j
  ... | nothing | [ Gᵢⱼ≡nothing ] = contradiction (≡-trans (≡-trans (≡-sym Gᵢⱼ≡v) (cong (G i) (≡-sym j≡p₀))) Gᵢⱼ≡nothing) λ() 
  ... | just w  | _              with j ≟ᶠ source p | i ∉? p | (i , j) ᵉ∈ᵍ? G
  ...   | no  j≢p₀ | _       | _              = contradiction j≡p₀ j≢p₀
  ...   | yes _    | no  i∈p | _              = contradiction i∉p i∈p
  ...   | yes _    | yes _   | no  eᵢⱼ∉G       = contradiction (v , subst (λ w → G i w ≡ cedge v) (≡-sym j≡p₀) Gᵢⱼ≡v) eᵢⱼ∉G
  ...   | yes _    | yes _   | yes (z , Gᵢⱼ≡z) = crouteEq (reflexive (cong (_▷ x) (just-injective ((≡-trans (≡-trans (≡-sym Gᵢⱼ≡z) (cong (G i) j≡p₀)) Gᵢⱼ≡v))))) (≡-refl ∷ ≈ₚ-refl)
