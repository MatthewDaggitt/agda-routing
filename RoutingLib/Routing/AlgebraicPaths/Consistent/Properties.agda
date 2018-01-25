open import Level using (_⊔_)
open import Data.Nat using (ℕ; suc; zero; _≤_; _<_; s≤s; z≤n)
open import Data.Sum using (inj₁; inj₂; _⊎_)
open import Relation.Nullary using (¬_; yes; no)
open import Data.Product using (∄; ∃; _×_; _,_)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Fin.Properties using () renaming (_≟_ to _≟𝔽_)
open import Data.List using (List; []; _∷_; map)
open import Data.List.Any using (here; there)
open import Data.Maybe using (just; nothing; Eq)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary using (Decidable; Rel; IsDecEquivalence; Transitive)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; subst; inspect; [_]; cong) renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans)
open import Algebra.FunctionProperties using (Op₂; Selective; Idempotent; Associative; Commutative; RightIdentity; RightZero)

open import RoutingLib.Routing.Definitions
open import RoutingLib.Data.Graph using (Graph; _∈?_)
open import RoutingLib.Data.Graph.SimplePath using ([]; [_]; _∷_∣_; _∺_∣_; source; _∈𝔾_) renaming (_≈_ to _≈ₚ_; _≉_ to _≉ₚ_)
open import RoutingLib.Data.Graph.SimplePath.Properties using (ℙₛ; _∈𝔾?_; ∈𝔾-resp-≈; weight-cong; _≤ₚ?_; ≤ₚ-antisym; ≤ₚ-trans; ≤ₚ-total; _∉?_; p≉i∷p; i∷p≰p) renaming (_≟_ to _≟ₚ_; ≈-refl to ≈ₚ-refl; ≈-sym to ≈ₚ-sym)
open import RoutingLib.Data.Graph.SimplePath.Enumeration using (allPaths; ∈-allPaths; allPaths!)
open import RoutingLib.Data.Maybe.Properties using (just-injective)
open import RoutingLib.Data.List.All using (_∷_)
open import RoutingLib.Data.List.All.Properties using (All-gfilter⁺₂)
open import RoutingLib.Data.List.Uniqueness.Setoid using (Unique)
open import RoutingLib.Data.List.Uniqueness.Setoid.Properties using (gfilter!⁺)
open import RoutingLib.Data.List.Membership.Setoid.Properties using (∈-map⁺; ∈-resp-≈; ∈-gfilter)
open import RoutingLib.Data.List.Uniset using (Uniset; IsEnumeration; Enumeration)
open import RoutingLib.Data.List.Properties using (foldr-map-commute)
open import RoutingLib.Routing.BellmanFord.DistanceVector.SufficientConditions using () renaming (SufficientConditions to SufficientConditions)
open import RoutingLib.Routing.BellmanFord.PathVector.SufficientConditions using (PathSufficientConditions)

module RoutingLib.Routing.AlgebraicPaths.Consistent.Properties
  {a b ℓ}
  (𝓡𝓐 : RoutingAlgebra a b ℓ)
  (⊕-sel : Selective (RoutingAlgebra._≈_ 𝓡𝓐) (RoutingAlgebra._⊕_ 𝓡𝓐))
  {n : ℕ}
  (G : Graph (RoutingAlgebra.Step 𝓡𝓐) n)
  where

  open RoutingAlgebra 𝓡𝓐
  open import RoutingLib.Routing.AlgebraicPaths.Consistent 𝓡𝓐 ⊕-sel G
  open import RoutingLib.Algebra.Selectivity.Properties using () renaming (idem to sel⇨idem)
  open import RoutingLib.Algebra.Selectivity.NaturalOrders S _⊕_ ⊕-cong using (_≤ᵣ_; ≤ᵣ-trans; ≤ᵣ⇨≤ₗ; ≤ₗ⇨≤ᵣ)

  open import Data.List.Any.Membership ℂₛ using (_∈_)

  abstract

    -------------------
    -- ⊕ᶜ properties --
    -------------------

    ⊕ᶜ-sel : Selective _≈ᶜ_ _⊕ᶜ_
    ⊕ᶜ-sel cnull          _              = inj₂ ≈ᶜ-refl
    ⊕ᶜ-sel (croute _ _ _ _) cnull          = inj₁ ≈ᶜ-refl
    ⊕ᶜ-sel (croute x p _ _) (croute y q _ _) with ⊕-select x y
    ... | sel₁ _ _ = inj₁ ≈ᶜ-refl
    ... | sel₂ _ _ = inj₂ ≈ᶜ-refl
    ... | sel≈ _ _ with p ≤ₚ? q
    ...   | yes _ = inj₁ ≈ᶜ-refl
    ...   | no  _ = inj₂ ≈ᶜ-refl

    ⊕ᶜ-idem : Idempotent _≈ᶜ_ _⊕ᶜ_
    ⊕ᶜ-idem = sel⇨idem _≈ᶜ_ _⊕ᶜ_ ⊕ᶜ-sel

    ⊕ᶜ-comm : Commutative _≈_ _⊕_ → Commutative _≈ᶜ_ _⊕ᶜ_
    ⊕ᶜ-comm _    cnull            cnull            = ≈ᶜ-refl
    ⊕ᶜ-comm _    cnull            (croute _ _ _ _) = ≈ᶜ-refl
    ⊕ᶜ-comm _    (croute _ _ _ _) cnull            = ≈ᶜ-refl
    ⊕ᶜ-comm comm (croute x p _ _) (croute y q _ _) with ⊕-select x y | ⊕-select y x
    ... | sel₁ x⊕y≈x _     | sel₁ _     y⊕x≉x = contradiction (≈-trans (comm y x) x⊕y≈x) y⊕x≉x
    ... | sel₁ _     _     | sel₂ _     _     = ≈ᶜ-refl
    ... | sel₁ _     x⊕y≉y | sel≈ y⊕x≈y _     = contradiction (≈-trans (comm x y) y⊕x≈y) x⊕y≉y
    ... | sel₂ _ _         | sel₁ _     _     = ≈ᶜ-refl
    ... | sel₂ x⊕y≉x _     | sel₂ _     y⊕x≈x = contradiction (≈-trans (comm x y) y⊕x≈x) x⊕y≉x
    ... | sel₂ x⊕y≉x _     | sel≈ _     y⊕x≈x = contradiction (≈-trans (comm x y) y⊕x≈x) x⊕y≉x
    ... | sel≈ x⊕y≈x _     | sel₁ _     y⊕x≉x = contradiction (≈-trans (comm y x) x⊕y≈x) y⊕x≉x
    ... | sel≈ _     x⊕y≈y | sel₂ y⊕x≉y _     = contradiction (≈-trans (comm y x) x⊕y≈y) y⊕x≉y
    ... | sel≈ x⊕y≈x x⊕y≈y | sel≈ _     _     with p ≤ₚ? q | q ≤ₚ? p
    ...   | yes p≤q | yes q≤p = crouteEq (≈-trans (≈-sym x⊕y≈x) x⊕y≈y) (≤ₚ-antisym p≤q q≤p)
    ...   | yes _   | no  _   = ≈ᶜ-refl
    ...   | no  _   | yes _   = ≈ᶜ-refl
    ...   | no  p≰q | no  q≰p with ≤ₚ-total p q
    ...     | inj₁ p≤q = contradiction p≤q p≰q
    ...     | inj₂ q≤p = contradiction q≤p q≰p

    ⊕ᶜ-assoc : Commutative _≈_ _⊕_ → Associative _≈_ _⊕_ → Associative _≈ᶜ_ _⊕ᶜ_
    ⊕ᶜ-assoc comm assoc cnull            cnull            cnull            = ≈ᶜ-refl
    ⊕ᶜ-assoc comm assoc cnull            cnull            (croute _ _ _ _) = ≈ᶜ-refl
    ⊕ᶜ-assoc comm assoc cnull            (croute _ _ _ _) cnull            = ≈ᶜ-refl
    ⊕ᶜ-assoc comm assoc cnull            (croute _ _ _ _) (croute _ _ _ _) = ≈ᶜ-refl
    ⊕ᶜ-assoc comm assoc (croute _ _ _ _) cnull            cnull            = ≈ᶜ-refl
    ⊕ᶜ-assoc comm assoc (croute _ _ _ _) cnull            (croute _ _ _ _) = ≈ᶜ-refl
    ⊕ᶜ-assoc comm assoc (croute x p _ _) (croute y q _ _) cnull            with ⊕-select x y
    ... | sel₁ _ _ = ≈ᶜ-refl
    ... | sel₂ _ _ = ≈ᶜ-refl
    ... | sel≈ _ _ with p ≤ₚ? q
    ...   | yes _ = ≈ᶜ-refl
    ...   | no  _ = ≈ᶜ-refl
    ⊕ᶜ-assoc comm assoc (croute x p p∈G x≈w[p]) (croute y q q∈G y≈w[q]) (croute z r r∈G z≈w[r]) = res
      where
      res : (croute x p p∈G x≈w[p] ⊕ᶜ croute y q q∈G y≈w[q]) ⊕ᶜ croute z r r∈G z≈w[r] ≈ᶜ croute x p p∈G x≈w[p] ⊕ᶜ (croute y q q∈G y≈w[q] ⊕ᶜ croute z r r∈G z≈w[r])
      res with ⊕-select x y | ⊕-select y z
      res | sel₁ _   _   | sel₁ _   _   with ⊕-select x y | ⊕-select x z
      res | sel₁ _   _   | sel₁ _   _   | sel₁ _   _   | sel₁ _   _   = ≈ᶜ-refl
      res | sel₁ x≤y _   | sel₁ _   z≰y | sel₁ _   _   | sel₂ _   z≤x = contradiction (≤ᵣ-trans assoc z≤x (≤ₗ⇨≤ᵣ comm x≤y)) z≰y
      res | sel₁ x≤y _   | sel₁ _   z≰y | sel₁ _   _   | sel≈ _   z≤x = contradiction (≤ᵣ-trans assoc z≤x (≤ₗ⇨≤ᵣ comm x≤y)) z≰y
      res | sel₁ x≤y _   | sel₁ _   _   | sel₂ x≰y _   | _            = contradiction x≤y x≰y
      res | sel₁ _   y≰x | sel₁ _   _   | sel≈ _   y≤x | _            = contradiction y≤x y≰x
      res | sel₁ _   _   | sel₂ _   _   = ≈ᶜ-refl
      res | sel₁ _   _   | sel≈ _   _   with q ≤ₚ? r
      res | sel₁ _   _   | sel≈ _   _   | yes _        with ⊕-select x y | ⊕-select x z
      res | sel₁ _   _   | sel≈ _   _   | yes _        | sel₁ _   _   | sel₁ _   _   = ≈ᶜ-refl
      res | sel₁ x≤y _   | sel≈ y≤z _   | yes _        | sel₁ _   _   | sel₂ x≰z _   = contradiction (≤ᵣ⇨≤ₗ comm (≤ᵣ-trans assoc (≤ₗ⇨≤ᵣ comm x≤y) (≤ₗ⇨≤ᵣ comm y≤z))) x≰z
      res | sel₁ _   y≰x | sel≈ y≤z _   | yes _        | sel₁ _   _   | sel≈ _   z≤x = contradiction (≤ᵣ-trans assoc (≤ₗ⇨≤ᵣ comm y≤z) z≤x) y≰x
      res | sel₁ x≤y _   | sel≈ _   _   | yes _        | sel₂ x≰y _   | _            = contradiction x≤y x≰y
      res | sel₁ _   y≰x | sel≈ _   _   | yes _        | sel≈ _   y≤x | _            = contradiction y≤x y≰x
      res | sel₁ _   _   | sel≈ _   _   | no  _        = ≈ᶜ-refl
      res | sel₂ _   _   | sel₁ _   _   with ⊕-select x y | ⊕-select y z
      res | sel₂ _   y≤x | sel₁ _   _   | sel₁ _   y≰x | _            = contradiction y≤x y≰x
      res | sel₂ _   _   | sel₁ _   _   | sel₂ _   _   | sel₁ _   _   = ≈ᶜ-refl
      res | sel₂ x≰y _   | sel₁ _   _   | sel≈ x≤y _   | _            = contradiction x≤y x≰y
      res | sel₂ _   _   | sel₁ y≤z _   | _            | sel₂ y≰z _   = contradiction y≤z y≰z
      res | sel₂ _   _   | sel₁ _   z≰y | _            | sel≈ _   z≤y = contradiction z≤y z≰y
      res | sel₂ _   _   | sel₂ _   _   with ⊕-select x z | ⊕-select y z
      res | sel₂ _   _   | sel₂ _   z≤y | _            | sel₁ _   z≰y = contradiction z≤y z≰y
      res | sel₂ x≰y _   | sel₂ _   z≤y | sel₁ x≤z _   | sel₂ _   _   = contradiction (≤ᵣ⇨≤ₗ comm (≤ᵣ-trans assoc (≤ₗ⇨≤ᵣ comm x≤z) z≤y)) x≰y
      res | sel₂ _   _   | sel₂ _   _   | sel₂ _   _   | sel₂ _   _   = ≈ᶜ-refl
      res | sel₂ x≰y _   | sel₂ _   z≤y | sel≈ x≤z _   | sel₂ _   _   = contradiction (≤ᵣ⇨≤ₗ comm (≤ᵣ-trans assoc (≤ₗ⇨≤ᵣ comm x≤z) z≤y)) x≰y
      res | sel₂ _   _   | sel₂ y≰z _   | _            | sel≈ y≤z _   = contradiction y≤z y≰z
      res | sel₂ _   _   | sel≈ _   _   with q ≤ₚ? r
      res | sel₂ _   _   | sel≈ _   _   | yes _        with ⊕-select x y | ⊕-select y z
      res | sel₂ _   y≤x | sel≈ _   _   | yes _        | sel₁ _   y≰x | _            = contradiction y≤x y≰x
      res | sel₂ _   _   | sel≈ _   z≤y | yes _        | _            | sel₁ _   z≰y = contradiction z≤y z≰y
      res | sel₂ _   _   | sel≈ y≤z _   | yes _        | _            | sel₂ y≰z _   = contradiction y≤z y≰z
      res | sel₂ _   _   | sel≈ _   _   | yes _        | sel₂ _   _   | sel≈ _   _   with q ≤ₚ? r
      res | sel₂ _   _   | sel≈ _   _   | yes _        | sel₂ _   _   | sel≈ _   _   | yes _        = ≈ᶜ-refl
      res | sel₂ _   _   | sel≈ _   _   | yes q≤r      | sel₂ _   _   | sel≈ _   _   | no  q≰r      = contradiction q≤r q≰r
      res | sel₂ x≰y _   | sel≈ _   _   | yes _        | sel≈ x≤y _   | _            = contradiction x≤y x≰y
      res | sel₂ _   _   | sel≈ _   _   | no  _        with ⊕-select x z | ⊕-select y z
      res | sel₂ _   _   | sel≈ _   z≤y | no  _        | _            | sel₁ _   z≰y = contradiction z≤y z≰y
      res | sel₂ _   _   | sel≈ y≤z _   | no  _        | _            | sel₂ y≰z _   = contradiction y≤z y≰z
      res | sel₂ x≰y _   | sel≈ _   z≤y | no  _        | sel₁ x≤z _   | sel≈ _   _   = contradiction (≤ᵣ⇨≤ₗ comm (≤ᵣ-trans assoc (≤ₗ⇨≤ᵣ comm x≤z) z≤y)) x≰y
      res | sel₂ _   _   | sel≈ _   _   | no  _        | sel₂ _   _   | sel≈ _   _   with q ≤ₚ? r
      res | sel₂ _   _   | sel≈ _   _   | no  q≰r      | sel₂ _   _   | sel≈ _   _   | yes q≤r      = contradiction q≤r q≰r
      res | sel₂ _   _   | sel≈ _   _   | no  _        | sel₂ _   _   | sel≈ _   _   | no  _        = ≈ᶜ-refl
      res | sel₂ x≰y _   | sel≈ _   z≤y | no  _        | sel≈ x≤z _   | sel≈ _   _   = contradiction (≤ᵣ⇨≤ₗ comm (≤ᵣ-trans assoc (≤ₗ⇨≤ᵣ comm x≤z) z≤y)) x≰y
      res | sel≈ _   _   | sel₁ _   _   with p ≤ₚ? q
      res | sel≈ _   _   | sel₁ _   _   | yes _        with ⊕-select x y | ⊕-select x z
      res | sel≈ _   y≤x | sel₁ _   _   | yes _        | sel₁ _   y≰x | _            = contradiction y≤x y≰x
      res | sel≈ x≤y _   | sel₁ _   _   | yes _        | sel₂ x≰y _   | _            = contradiction x≤y x≰y
      res | sel≈ _   _   | sel₁ _   _   | yes _        | sel≈ _   _   | sel₁ _   _   with p ≤ₚ? q
      res | sel≈ _   _   | sel₁ _   _   | yes _        | sel≈ _   _   | sel₁ _   _   | yes _         = ≈ᶜ-refl
      res | sel≈ _   _   | sel₁ _   _   | yes p≤q      | sel≈ _   _   | sel₁ _   _   | no  p≰q       = contradiction p≤q p≰q
      res | sel≈ x≤y _   | sel₁ _   z≰y | yes _        | sel≈ _   _   | sel₂ _   z≤x = contradiction (≤ᵣ-trans assoc z≤x (≤ₗ⇨≤ᵣ comm x≤y)) z≰y
      res | sel≈ x≤y _   | sel₁ _   z≰y | yes _        | sel≈ _   _   | sel≈ _   z≤x = contradiction (≤ᵣ-trans assoc z≤x (≤ₗ⇨≤ᵣ comm x≤y)) z≰y
      res | sel≈ _   _   | sel₁ _   _   | no  _        with ⊕-select x y | ⊕-select y z
      res | sel≈ _   y≤x | sel₁ _   _   | no  _        | sel₁ _   y≰x | _            = contradiction y≤x y≰x
      res | sel≈ x≤y _   | sel₁ _   _   | no  _        | sel₂ x≰y _   | _            = contradiction x≤y x≰y
      res | sel≈ _   _   | sel₁ _   _   | no  _        | sel≈ _   _   | sel₁ _   _   with p ≤ₚ? q
      res | sel≈ _   _   | sel₁ _   _   | no  p≰q      | sel≈ _   _   | sel₁ _   _   | yes p≤q      = contradiction p≤q p≰q
      res | sel≈ _   _   | sel₁ _   _   | no  _        | sel≈ _   _   | sel₁ _   _   | no  _        = ≈ᶜ-refl
      res | sel≈ _   _   | sel₁ x≤y _   | no  _        | _            | sel₂ x≰y _   = contradiction x≤y x≰y
      res | sel≈ _   _   | sel₁ _   y≰x | no  _        | _            | sel≈ _   y≤x = contradiction y≤x y≰x
      res | sel≈ _   _   | sel₂ _   _   with p ≤ₚ? q
      res | sel≈ _   _   | sel₂ _   _   | yes _        = ≈ᶜ-refl
      res | sel≈ _   _   | sel₂ _   _   | no  _        with ⊕-select x z | ⊕-select y z
      res | sel≈ _   _   | sel₂ _   z≤y | no  _        | _            | sel₁ _   z≰y = contradiction z≤y z≰y
      res | sel≈ _   y≤x | sel₂ y≰z _   | no  _        | sel₁ x≤z _   | sel₂ _   _   = contradiction (≤ᵣ⇨≤ₗ comm (≤ᵣ-trans assoc y≤x (≤ₗ⇨≤ᵣ comm x≤z))) y≰z
      res | sel≈ _   _   | sel₂ _   _   | no  _        | sel₂ _   _   | sel₂ _   _   = ≈ᶜ-refl
      res | sel≈ _   y≤x | sel₂ y≰z _   | no  _        | sel≈ x≤z _   | sel₂ _   _   = contradiction (≤ᵣ⇨≤ₗ comm (≤ᵣ-trans assoc y≤x (≤ₗ⇨≤ᵣ comm x≤z))) y≰z
      res | sel≈ _   _   | sel₂ y≰z _   | no  _        | _            | sel≈ y≤z _   = contradiction y≤z y≰z
      res | sel≈ _   _   | sel≈ _   _   with p ≤ₚ? q | q ≤ₚ? r
      res | sel≈ _   _   | sel≈ _   _   | yes _        | yes _        with ⊕-select x y | ⊕-select x z
      res | sel≈ _   y≤x | sel≈ _   _   | yes _        | yes _        | sel₁ _   y≰x | _            = contradiction y≤x y≰x
      res | sel≈ x≤y _   | sel≈ _   _   | yes _        | yes _        | sel₂ x≰y _   | _            = contradiction x≤y x≰y
      res | sel≈ _   y≤x | sel≈ _   z≤y | yes _        | yes _        | sel≈ _   _   | sel₁ _   z≰x = contradiction (≤ᵣ-trans assoc z≤y y≤x) z≰x
      res | sel≈ x≤y _   | sel≈ y≤z _   | yes _        | yes _        | sel≈ _   _   | sel₂ x≰z _   = contradiction (≤ᵣ⇨≤ₗ comm (≤ᵣ-trans assoc (≤ₗ⇨≤ᵣ comm x≤y) (≤ₗ⇨≤ᵣ comm y≤z))) x≰z
      res | sel≈ _   _   | sel≈ _   _   | yes _        | yes _        | sel≈ _   _   | sel≈ _   _   with p ≤ₚ? q | p ≤ₚ? r
      res | sel≈ _   _   | sel≈ _   _   | yes _        | yes _        | sel≈ _   _   | sel≈ _   _   | yes _       | yes _      = ≈ᶜ-refl
      res | sel≈ _   _   | sel≈ _   _   | yes p≤q      | yes q≤r      | sel≈ _   _   | sel≈ _   _   | yes _       | no  p≰r    = contradiction (≤ₚ-trans p≤q q≤r) p≰r
      res | sel≈ _   _   | sel≈ _   _   | yes p≤q      | yes _        | sel≈ _   _   | sel≈ _   _   | no  p≰q     | _          = contradiction p≤q p≰q
      res | sel≈ _   _   | sel≈ _   _   | yes _        | no  _        = ≈ᶜ-refl
      res | sel≈ _   _   | sel≈ _   _   | no  _        | yes _        with ⊕-select x y | ⊕-select y z
      res | sel≈ _   y≤x | sel≈ _   _   | no  _        | yes _        | sel₁ _   y≰x | _            = contradiction y≤x y≰x
      res | sel≈ x≤y _   | sel≈ _   _   | no  _        | yes _        | sel₂ x≰y _   | _            = contradiction x≤y x≰y
      res | sel≈ _   _   | sel≈ _   z≤y | no  _        | yes _        | _            | sel₁ _   z≰y = contradiction z≤y z≰y
      res | sel≈ _   _   | sel≈ y≤z _   | no  _        | yes _        | _            | sel₂ y≰z _   = contradiction y≤z y≰z
      res | sel≈ _   _   | sel≈ _   _   | no  _        | yes _        | sel≈ _   _   | sel≈ _   _   with p ≤ₚ? q | q ≤ₚ? r
      res | sel≈ _   _   | sel≈ _   _   | no  p≰q      | yes _        | sel≈ _   _   | sel≈ _   _   | yes p≤q     | _          = contradiction p≤q p≰q
      res | sel≈ _   _   | sel≈ _   _   | no  _        | yes q≤r      | sel≈ _   _   | sel≈ _   _   | _           | no  q≰r    = contradiction q≤r q≰r
      res | sel≈ _   _   | sel≈ _   _   | no  _        | yes _        | sel≈ _   _   | sel≈ _   _   | no  _       | yes _      = ≈ᶜ-refl
      res | sel≈ _   _   | sel≈ _   _   | no  _        | no  _        with ⊕-select x z | ⊕-select y z
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
    ⊕ᶜ-almost-strictly-absorbs-▷ᶜ abs (i , j) {croute x [] [] x≈1} _    with i ≟𝔽 j | (i , j) ∈? G
    ... | yes _   | _       = ≈ᶜ-refl , λ()
    ... | no  _   | no  _   = ≈ᶜ-refl , λ()
    ... | no  i≢j | yes (v , b) with v ▷ x ≟ 0#
    ...   | yes _ = ≈ᶜ-refl , λ()
    ...   | no  _ with ⊕-select (v ▷ x) x
    ...     | sel₁ _ vx⊕x≉x = contradiction (abs v x) vx⊕x≉x
    ...     | sel₂ _ _      = ≈ᶜ-refl , λ{(crouteEq x≈vx ())}
    ...     | sel≈ _ _      with [ i ∺ j ∣ i≢j ] ≤ₚ? []
    ...       | yes ()
    ...       | no  _ = ≈ᶜ-refl , λ{(crouteEq x≈vx ())}
    ⊕ᶜ-almost-strictly-absorbs-▷ᶜ abs (i , j) {croute x [ p ] [ p∈G ] x≈w[p]} _    with j ≟𝔽 source p | i ∉? [ p ] | (i , j) ∈? G
    ... | no  _    | _           | _              = ≈ᶜ-refl , λ()
    ... | yes _    | no  _       | _              = ≈ᶜ-refl , λ()
    ... | yes _    | yes _       | no  _          = ≈ᶜ-refl , λ()
    ... | yes j≡p₀ | yes [ i∉p ] | yes (v , Gᵢⱼ≡v) with v ▷ x ≟ 0#
    ...   | yes _ = ≈ᶜ-refl , λ()
    ...   | no  _ with ⊕-select (v ▷ x) x
    ...     | sel₁ _       vx⊕x≉x = contradiction (abs v x) vx⊕x≉x
    ...     | sel₂ vx⊕x≉vx _      = ≈ᶜ-refl , λ{(crouteEq _ [ p≈i∷p ]) → p≉i∷p p≈i∷p}
    ...     | sel≈ _       _      with [ i ∷ p ∣ i∉p ] ≤ₚ? [ p ]
    ...       | yes i∷p≤p = contradiction i∷p≤p i∷p≰p
    ...       | no  i∷p≰p = ≈ᶜ-refl , λ{(crouteEq _ [ p≈i∷p ]) → p≉i∷p p≈i∷p}


    -----------------------------------------
    -- Identity and annihilator properties --
    -----------------------------------------

    cnull-idᵣ-⊕ᶜ : RightIdentity _≈ᶜ_ cnull _⊕ᶜ_
    cnull-idᵣ-⊕ᶜ cnull           = ≈ᶜ-refl
    cnull-idᵣ-⊕ᶜ (croute x p _ _) = ≈ᶜ-refl

    cnull-anᵣ-▷ᶜ : ∀ e → e ▷ᶜ cnull ≈ᶜ cnull
    cnull-anᵣ-▷ᶜ _ = ≈ᶜ-refl

    1[]-anᵣ-⊕ᶜ : RightZero _≈_ 1# _⊕_ → RightZero _≈ᶜ_ (croute 1# [] [] ≈-refl) _⊕ᶜ_
    1[]-anᵣ-⊕ᶜ rz cnull = ≈ᶜ-refl
    1[]-anᵣ-⊕ᶜ rz (croute x p p∈G x≈wp) with ⊕-select x 1#
    ... | sel₁ _ x⊕1≉1 = contradiction (rz x) x⊕1≉1
    ... | sel₂ _ _     = ≈ᶜ-refl
    ... | sel≈ _ _     with p | p∈G | p ≤ₚ? []
    ...   | _     | _  | no  _ = ≈ᶜ-refl
    ...   | []    | [] | yes _ = crouteEq x≈wp []
    ...   | [ _ ] | _  | yes ()

    -------------------------
    -- Conversion of paths --
    -------------------------

    pathToCRoute-cong : ∀ {p q} → p ≈ₚ q → (p∈G : p ∈𝔾 G) (q∈G : q ∈𝔾 G) → pathToCRoute p∈G ≈ᶜ pathToCRoute q∈G
    pathToCRoute-cong p≈q p∈G q∈G = crouteEq (≈-reflexive (weight-cong _▷_ 1# p≈q p∈G q∈G)) p≈q

    pathToCRoute-¬cong : ∀ {p q} → p ≉ₚ q → (p∈G : p ∈𝔾 G) (q∈G : q ∈𝔾 G) → pathToCRoute p∈G ≉ᶜ pathToCRoute q∈G
    pathToCRoute-¬cong p≉q _ _ (crouteEq _ p≈q) = p≉q p≈q
    
    pathToCRouteMaybe-cong : ∀ {p q} → p ≈ₚ q → Eq _≈ᶜ_ (pathToCRouteMaybe p) (pathToCRouteMaybe q)
    pathToCRouteMaybe-cong {p} {q} p≈q with p ∈𝔾? G | q ∈𝔾? G
    ... | yes _   | yes _   = just (pathToCRoute-cong p≈q _ _)
    ... | yes p∈G | no  q∉G = contradiction (∈𝔾-resp-≈ p≈q p∈G) q∉G
    ... | no  p∉G | yes q∈G = contradiction (∈𝔾-resp-≈ (≈ₚ-sym p≈q) q∈G) p∉G
    ... | no  _   | no  _   = nothing

    pathToCRouteMaybe-¬cong : ∀ {p q} → p ≉ₚ q → pathToCRouteMaybe p ≡ nothing ⊎ pathToCRouteMaybe q ≡ nothing ⊎ Eq _≉ᶜ_ (pathToCRouteMaybe p) (pathToCRouteMaybe q)
    pathToCRouteMaybe-¬cong {p} {q} p≉q with p ∈𝔾? G | q ∈𝔾? G
    ... | yes _ | yes _ = inj₂ (inj₂ (just (pathToCRoute-¬cong p≉q _ _)))
    ... | _     | no _  = inj₂ (inj₁ ≡-refl)
    ... | no _  | _     = inj₁ (≡-refl)

    cnull≉pathToCRouteMaybe : ∀ {p r} → pathToCRouteMaybe p ≡ just r → cnull ≉ᶜ r
    cnull≉pathToCRouteMaybe {p} {r} with p ∈𝔾? G
    ... | yes _ = λ {≡-refl ()}
    ... | no  _ = λ()

    pathToCRouteMaybe≈xp : ∀ {p} (p∈G : p ∈𝔾 G) {x} (x≈w[p] : x ≈ weight p∈G) → Eq _≈ᶜ_ (pathToCRouteMaybe p) (just (croute x p p∈G x≈w[p]))
    pathToCRouteMaybe≈xp {p} p∈G x≈w[p] with p ∈𝔾? G
    ... | yes p∈G' = just (crouteEq (≈-sym (≈-trans x≈w[p] (≈-reflexive (weight-cong _▷_ 1# ≈ₚ-refl p∈G p∈G')))) ≈ₚ-refl)
    ... | no  p∉G  = contradiction p∈G p∉G


    ---------------
    -- All paths --
    ---------------
    
    allCRoutes! : Unique ℂₛ (allCRoutes)
    allCRoutes! = All-gfilter⁺₂ cnull≉pathToCRouteMaybe (allPaths n) ∷ gfilter!⁺ ℙₛ ℂₛ pathToCRouteMaybe pathToCRouteMaybe-¬cong (allPaths! n)

    ∈-allCRoutes : ∀ r → r ∈ allCRoutes
    ∈-allCRoutes cnull                   = here cnullEq
    ∈-allCRoutes (croute x p p∈G x≈w[p]) = there (∈-gfilter ℙₛ ℂₛ pathToCRouteMaybe (∈-allPaths p) (pathToCRouteMaybe≈xp p∈G x≈w[p]) pathToCRouteMaybe-cong)

  ℂ-enumeration : Enumeration Decℂₛ
  ℂ-enumeration = record
    { X             = allCRoutes , allCRoutes!
    ; isEnumeration = ∈-allCRoutes
    }
  
  -----------
  -- Other --
  -----------

  abstract

    convertSufficientConditions : PathSufficientConditions ? → SufficientConditions 𝓡𝓐ᶜ
    convertSufficientConditions psc = record
      { ⊕-assoc                     = ⊕ᶜ-assoc {!⊕-comm!} {!!}
      ; ⊕-sel                       = {!!}
      ; ⊕-comm                      = {!!}
      ; ⊕-almost-strictly-absorbs-▷ = {!!}
      ; 0#-idᵣ-⊕                    = {!!}
      ; 0#-an-▷                     = {!!}
      ; 1#-anᵣ-⊕                    = {!!}
      ; routes-enumerable           = ℂ-enumeration
      }
      where open PathSufficientConditions psc
{-
      record 
      { ⊕-assoc                     = ⊕ᶜ-assoc ⊕-comm ⊕-assoc
      ; ⊕-sel                       = ⊕ᶜ-sel
      ; ⊕-comm                      = ⊕ᶜ-comm ⊕-comm
      ; ⊕-almost-strictly-absorbs-▷ = ⊕ᶜ-almost-strictly-absorbs-▷ᶜ {!!} --⊕-absorbs-▷

      ; 0#-idᵣ-⊕ = cnull-idᵣ-⊕ᶜ
      ; 0#-an-▷  = cnull-anᵣ-▷ᶜ
      ; 1#-anᵣ-⊕ = 1[]-anᵣ-⊕ᶜ 1#-anᵣ-⊕

      ; routes-enumerable = ℂ-enumeration
      }
      where open PathSufficientConditions psc
-}
