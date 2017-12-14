open import Level using (_⊔_)
open import Data.Nat using (ℕ; suc; zero; s≤s; z≤n; _<_; _≤_)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Nullary using (¬_; yes; no)
open import Data.Product using (∃₂; _×_; _,_)
open import Data.Fin using (Fin)
open import Data.Fin.Properties using () renaming (_≟_ to _≟𝔽_)
open import Data.Fin.Dec using (all?;  ¬∀⟶∃¬)
open import Data.Maybe using (just; nothing)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary using (Rel; IsDecEquivalence; Transitive)
open import Relation.Unary using (Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; subst) renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans)
open import Algebra.FunctionProperties using (Op₂; Selective; Idempotent; Associative; Commutative; RightIdentity; RightZero)

open import RoutingLib.Routing.Definitions
open import RoutingLib.Data.Graph using (Graph; _∈?_; ∈-resp-≡ₗ)
open import RoutingLib.Data.Graph.SimplePath hiding (weight) renaming (_≈_ to _≈ₚ_)
open import RoutingLib.Data.Graph.SimplePath.Properties renaming (_≟_ to _≟ₚ_; ≈-reflexive to ≈ₚ-reflexive; ≈-refl to ≈ₚ-refl; ≈-sym to ≈ₚ-sym; ≈-trans to ≈ₚ-trans; ∈𝔾-resp-≈ to ∈𝔾-resp-≈ₚ)
open import RoutingLib.Data.Graph.SimplePath.NonEmpty.Properties using (p≉i∷p)
open import RoutingLib.Algebra.FunctionProperties using (_×-Preserves_)

module RoutingLib.Routing.AlgebraicPaths.Inconsistent.Properties
  {a b ℓ}
  (𝓡𝓐 : RoutingAlgebra a b ℓ)
  (⊕-sel : Selective (RoutingAlgebra._≈_ 𝓡𝓐) (RoutingAlgebra._⊕_ 𝓡𝓐))
  {n : ℕ}
  (G : Graph (RoutingAlgebra.Step 𝓡𝓐) n)
  where

  open RoutingAlgebra 𝓡𝓐
  open import RoutingLib.Routing.AlgebraicPaths.Inconsistent 𝓡𝓐 ⊕-sel G
  open import RoutingLib.Algebra.Selectivity.Properties _≈_ _⊕_ ⊕-sel using () renaming (idem to ⊕-idem)
  open import RoutingLib.Algebra.Selectivity.NaturalOrders S _⊕_ ⊕-cong using (_≤ᵣ_; ≤ᵣ-trans; ≤ᵣ⇨≤ₗ; ≤ₗ⇨≤ᵣ)

  abstract

    -------------------
    -- ⊕ⁱ properties --
    -------------------

    ⊕ⁱ-sel : Selective _≈ⁱ_ _⊕ⁱ_
    ⊕ⁱ-sel inull          _          = inj₂ ≈ⁱ-refl
    ⊕ⁱ-sel (iroute _ _) inull        = inj₁ ≈ⁱ-refl
    ⊕ⁱ-sel (iroute x p) (iroute y q) with ⊕-select x y
    ... | sel₁ _ _ = inj₁ ≈ⁱ-refl
    ... | sel₂ _ _ = inj₂ ≈ⁱ-refl
    ... | sel≈ _ _ with p ≤ₚ? q
    ...   | yes _ = inj₁ ≈ⁱ-refl
    ...   | no  _ = inj₂ ≈ⁱ-refl

    ⊕ⁱ-comm : Commutative _≈_ _⊕_ → Commutative _≈ⁱ_ _⊕ⁱ_
    ⊕ⁱ-comm _    inull        inull        = ≈ⁱ-refl
    ⊕ⁱ-comm _    inull        (iroute _ _) = ≈ⁱ-refl
    ⊕ⁱ-comm _    (iroute _ _) inull        = ≈ⁱ-refl
    ⊕ⁱ-comm comm (iroute x p) (iroute y q) with ⊕-select x y | ⊕-select y x
    ... | sel₁ x⊕y≈x _     | sel₁ _     y⊕x≉x = contradiction (≈-trans (comm y x) x⊕y≈x) y⊕x≉x
    ... | sel₁ _     _     | sel₂ _     _     = ≈ⁱ-refl
    ... | sel₁ _     x⊕y≉y | sel≈ y⊕x≈y _     = contradiction (≈-trans (comm x y) y⊕x≈y) x⊕y≉y
    ... | sel₂ _ _         | sel₁ _     _     = ≈ⁱ-refl
    ... | sel₂ x⊕y≉x _     | sel₂ _     y⊕x≈x = contradiction (≈-trans (comm x y) y⊕x≈x) x⊕y≉x
    ... | sel₂ x⊕y≉x _     | sel≈ _     y⊕x≈x = contradiction (≈-trans (comm x y) y⊕x≈x) x⊕y≉x
    ... | sel≈ x⊕y≈x _     | sel₁ _     y⊕x≉x = contradiction (≈-trans (comm y x) x⊕y≈x) y⊕x≉x
    ... | sel≈ _     x⊕y≈y | sel₂ y⊕x≉y _     = contradiction (≈-trans (comm y x) x⊕y≈y) y⊕x≉y
    ... | sel≈ x⊕y≈x x⊕y≈y | sel≈ _     _     with p ≤ₚ? q | q ≤ₚ? p
    ...   | yes p≤q | yes q≤p = irouteEq (≈-trans (≈-sym x⊕y≈x) x⊕y≈y) (≤ₚ-antisym p≤q q≤p)
    ...   | yes _   | no  _   = ≈ⁱ-refl
    ...   | no  _   | yes _   = ≈ⁱ-refl
    ...   | no  p≰q | no  q≰p with ≤ₚ-total p q
    ...     | inj₁ p≤q = contradiction p≤q p≰q
    ...     | inj₂ q≤p = contradiction q≤p q≰p


    ⊕ⁱ-assoc : Commutative _≈_ _⊕_ → Associative _≈_ _⊕_ → Associative _≈ⁱ_ _⊕ⁱ_
    ⊕ⁱ-assoc comm assoc inull        inull        inull        = ≈ⁱ-refl
    ⊕ⁱ-assoc comm assoc inull        inull        (iroute _ _) = ≈ⁱ-refl
    ⊕ⁱ-assoc comm assoc inull        (iroute _ _) inull        = ≈ⁱ-refl
    ⊕ⁱ-assoc comm assoc inull        (iroute _ _) (iroute _ _) = ≈ⁱ-refl
    ⊕ⁱ-assoc comm assoc (iroute _ _) inull        inull        = ≈ⁱ-refl
    ⊕ⁱ-assoc comm assoc (iroute _ _) inull        (iroute _ _) = ≈ⁱ-refl
    ⊕ⁱ-assoc comm assoc (iroute x p) (iroute y q) inull        with ⊕-select x y
    ... | sel₁ _ _ = ≈ⁱ-refl
    ... | sel₂ _ _ = ≈ⁱ-refl
    ... | sel≈ _ _ with p ≤ₚ? q
    ...   | yes _ = ≈ⁱ-refl
    ...   | no  _ = ≈ⁱ-refl
    ⊕ⁱ-assoc comm assoc (iroute x p) (iroute y q) (iroute z r) = res

      where

      res : (iroute x p ⊕ⁱ iroute y q) ⊕ⁱ iroute z r ≈ⁱ iroute x p ⊕ⁱ (iroute y q ⊕ⁱ iroute z r)
      res with ⊕-select x y | ⊕-select y z
      res | sel₁ _   _   | sel₁ _   _   with ⊕-select x y | ⊕-select x z
      res | sel₁ _   _   | sel₁ _   _   | sel₁ _   _   | sel₁ _   _   = ≈ⁱ-refl
      res | sel₁ x≤y _   | sel₁ _   z≰y | sel₁ _   _   | sel₂ _   z≤x = contradiction (≤ᵣ-trans assoc z≤x (≤ₗ⇨≤ᵣ comm x≤y)) z≰y
      res | sel₁ x≤y _   | sel₁ _   z≰y | sel₁ _   _   | sel≈ _   z≤x = contradiction (≤ᵣ-trans assoc z≤x (≤ₗ⇨≤ᵣ comm x≤y)) z≰y
      res | sel₁ x≤y _   | sel₁ _   _   | sel₂ x≰y _   | _            = contradiction x≤y x≰y
      res | sel₁ _   y≰x | sel₁ _   _   | sel≈ _   y≤x | _            = contradiction y≤x y≰x
      res | sel₁ _   _   | sel₂ _   _   = ≈ⁱ-refl
      res | sel₁ _   _   | sel≈ _   _   with q ≤ₚ? r
      res | sel₁ _   _   | sel≈ _   _   | yes _        with ⊕-select x y | ⊕-select x z
      res | sel₁ _   _   | sel≈ _   _   | yes _        | sel₁ _   _   | sel₁ _   _   = ≈ⁱ-refl
      res | sel₁ x≤y _   | sel≈ y≤z _   | yes _        | sel₁ _   _   | sel₂ x≰z _   = contradiction (≤ᵣ⇨≤ₗ comm (≤ᵣ-trans assoc (≤ₗ⇨≤ᵣ comm x≤y) (≤ₗ⇨≤ᵣ comm y≤z))) x≰z
      res | sel₁ _   y≰x | sel≈ y≤z _   | yes _        | sel₁ _   _   | sel≈ _   z≤x = contradiction (≤ᵣ-trans assoc (≤ₗ⇨≤ᵣ comm y≤z) z≤x) y≰x
      res | sel₁ x≤y _   | sel≈ _   _   | yes _        | sel₂ x≰y _   | _            = contradiction x≤y x≰y
      res | sel₁ _   y≰x | sel≈ _   _   | yes _        | sel≈ _   y≤x | _            = contradiction y≤x y≰x
      res | sel₁ _   _   | sel≈ _   _   | no  _        = ≈ⁱ-refl
      res | sel₂ _   _   | sel₁ _   _   with ⊕-select x y | ⊕-select y z
      res | sel₂ _   y≤x | sel₁ _   _   | sel₁ _   y≰x | _            = contradiction y≤x y≰x
      res | sel₂ _   _   | sel₁ _   _   | sel₂ _   _   | sel₁ _   _   = ≈ⁱ-refl
      res | sel₂ x≰y _   | sel₁ _   _   | sel≈ x≤y _   | _            = contradiction x≤y x≰y
      res | sel₂ _   _   | sel₁ y≤z _   | _            | sel₂ y≰z _   = contradiction y≤z y≰z
      res | sel₂ _   _   | sel₁ _   z≰y | _            | sel≈ _   z≤y = contradiction z≤y z≰y
      res | sel₂ _   _   | sel₂ _   _   with ⊕-select x z | ⊕-select y z
      res | sel₂ _   _   | sel₂ _   z≤y | _            | sel₁ _   z≰y = contradiction z≤y z≰y
      res | sel₂ x≰y _   | sel₂ _   z≤y | sel₁ x≤z _   | sel₂ _   _   = contradiction (≤ᵣ⇨≤ₗ comm (≤ᵣ-trans assoc (≤ₗ⇨≤ᵣ comm x≤z) z≤y)) x≰y
      res | sel₂ _   _   | sel₂ _   _   | sel₂ _   _   | sel₂ _   _   = ≈ⁱ-refl
      res | sel₂ x≰y _   | sel₂ _   z≤y | sel≈ x≤z _   | sel₂ _   _   = contradiction (≤ᵣ⇨≤ₗ comm (≤ᵣ-trans assoc (≤ₗ⇨≤ᵣ comm x≤z) z≤y)) x≰y
      res | sel₂ _   _   | sel₂ y≰z _   | _            | sel≈ y≤z _   = contradiction y≤z y≰z
      res | sel₂ _   _   | sel≈ _   _   with q ≤ₚ? r
      res | sel₂ _   _   | sel≈ _   _   | yes _        with ⊕-select x y | ⊕-select y z
      res | sel₂ _   y≤x | sel≈ _   _   | yes _        | sel₁ _   y≰x | _            = contradiction y≤x y≰x
      res | sel₂ _   _   | sel≈ _   z≤y | yes _        | _            | sel₁ _   z≰y = contradiction z≤y z≰y
      res | sel₂ _   _   | sel≈ y≤z _   | yes _        | _            | sel₂ y≰z _   = contradiction y≤z y≰z
      res | sel₂ _   _   | sel≈ _   _   | yes _        | sel₂ _   _   | sel≈ _   _   with q ≤ₚ? r
      res | sel₂ _   _   | sel≈ _   _   | yes _        | sel₂ _   _   | sel≈ _   _   | yes _        = ≈ⁱ-refl
      res | sel₂ _   _   | sel≈ _   _   | yes q≤r      | sel₂ _   _   | sel≈ _   _   | no  q≰r      = contradiction q≤r q≰r
      res | sel₂ x≰y _   | sel≈ _   _   | yes _        | sel≈ x≤y _   | _            = contradiction x≤y x≰y
      res | sel₂ _   _   | sel≈ _   _   | no  _        with ⊕-select x z | ⊕-select y z
      res | sel₂ _   _   | sel≈ _   z≤y | no  _        | _            | sel₁ _   z≰y = contradiction z≤y z≰y
      res | sel₂ _   _   | sel≈ y≤z _   | no  _        | _            | sel₂ y≰z _   = contradiction y≤z y≰z
      res | sel₂ x≰y _   | sel≈ _   z≤y | no  _        | sel₁ x≤z _   | sel≈ _   _   = contradiction (≤ᵣ⇨≤ₗ comm (≤ᵣ-trans assoc (≤ₗ⇨≤ᵣ comm x≤z) z≤y)) x≰y
      res | sel₂ _   _   | sel≈ _   _   | no  _        | sel₂ _   _   | sel≈ _   _   with q ≤ₚ? r
      res | sel₂ _   _   | sel≈ _   _   | no  q≰r      | sel₂ _   _   | sel≈ _   _   | yes q≤r      = contradiction q≤r q≰r
      res | sel₂ _   _   | sel≈ _   _   | no  _        | sel₂ _   _   | sel≈ _   _   | no  _        = ≈ⁱ-refl
      res | sel₂ x≰y _   | sel≈ _   z≤y | no  _        | sel≈ x≤z _   | sel≈ _   _   = contradiction (≤ᵣ⇨≤ₗ comm (≤ᵣ-trans assoc (≤ₗ⇨≤ᵣ comm x≤z) z≤y)) x≰y
      res | sel≈ _   _   | sel₁ _   _   with p ≤ₚ? q
      res | sel≈ _   _   | sel₁ _   _   | yes _        with ⊕-select x y | ⊕-select x z
      res | sel≈ _   y≤x | sel₁ _   _   | yes _        | sel₁ _   y≰x | _            = contradiction y≤x y≰x
      res | sel≈ x≤y _   | sel₁ _   _   | yes _        | sel₂ x≰y _   | _            = contradiction x≤y x≰y
      res | sel≈ _   _   | sel₁ _   _   | yes _        | sel≈ _   _   | sel₁ _   _   with p ≤ₚ? q
      res | sel≈ _   _   | sel₁ _   _   | yes _        | sel≈ _   _   | sel₁ _   _   | yes _         = ≈ⁱ-refl
      res | sel≈ _   _   | sel₁ _   _   | yes p≤q      | sel≈ _   _   | sel₁ _   _   | no  p≰q       = contradiction p≤q p≰q
      res | sel≈ x≤y _   | sel₁ _   z≰y | yes _        | sel≈ _   _   | sel₂ _   z≤x = contradiction (≤ᵣ-trans assoc z≤x (≤ₗ⇨≤ᵣ comm x≤y)) z≰y
      res | sel≈ x≤y _   | sel₁ _   z≰y | yes _        | sel≈ _   _   | sel≈ _   z≤x = contradiction (≤ᵣ-trans assoc z≤x (≤ₗ⇨≤ᵣ comm x≤y)) z≰y
      res | sel≈ _   _   | sel₁ _   _   | no  _        with ⊕-select x y | ⊕-select y z
      res | sel≈ _   y≤x | sel₁ _   _   | no  _        | sel₁ _   y≰x | _            = contradiction y≤x y≰x
      res | sel≈ x≤y _   | sel₁ _   _   | no  _        | sel₂ x≰y _   | _            = contradiction x≤y x≰y
      res | sel≈ _   _   | sel₁ _   _   | no  _        | sel≈ _   _   | sel₁ _   _   with p ≤ₚ? q
      res | sel≈ _   _   | sel₁ _   _   | no  p≰q      | sel≈ _   _   | sel₁ _   _   | yes p≤q      = contradiction p≤q p≰q
      res | sel≈ _   _   | sel₁ _   _   | no  _        | sel≈ _   _   | sel₁ _   _   | no  _        = ≈ⁱ-refl
      res | sel≈ _   _   | sel₁ x≤y _   | no  _        | _            | sel₂ x≰y _   = contradiction x≤y x≰y
      res | sel≈ _   _   | sel₁ _   y≰x | no  _        | _            | sel≈ _   y≤x = contradiction y≤x y≰x
      res | sel≈ _   _   | sel₂ _   _   with p ≤ₚ? q
      res | sel≈ _   _   | sel₂ _   _   | yes _        = ≈ⁱ-refl
      res | sel≈ _   _   | sel₂ _   _   | no  _        with ⊕-select x z | ⊕-select y z
      res | sel≈ _   _   | sel₂ _   z≤y | no  _        | _            | sel₁ _   z≰y = contradiction z≤y z≰y
      res | sel≈ _   y≤x | sel₂ y≰z _   | no  _        | sel₁ x≤z _   | sel₂ _   _   = contradiction (≤ᵣ⇨≤ₗ comm (≤ᵣ-trans assoc y≤x (≤ₗ⇨≤ᵣ comm x≤z))) y≰z
      res | sel≈ _   _   | sel₂ _   _   | no  _        | sel₂ _   _   | sel₂ _   _   = ≈ⁱ-refl
      res | sel≈ _   y≤x | sel₂ y≰z _   | no  _        | sel≈ x≤z _   | sel₂ _   _   = contradiction (≤ᵣ⇨≤ₗ comm (≤ᵣ-trans assoc y≤x (≤ₗ⇨≤ᵣ comm x≤z))) y≰z
      res | sel≈ _   _   | sel₂ y≰z _   | no  _        | _            | sel≈ y≤z _   = contradiction y≤z y≰z
      res | sel≈ _   _   | sel≈ _   _   with p ≤ₚ? q | q ≤ₚ? r
      res | sel≈ _   _   | sel≈ _   _   | yes _        | yes _        with ⊕-select x y | ⊕-select x z
      res | sel≈ _   y≤x | sel≈ _   _   | yes _        | yes _        | sel₁ _   y≰x | _            = contradiction y≤x y≰x
      res | sel≈ x≤y _   | sel≈ _   _   | yes _        | yes _        | sel₂ x≰y _   | _            = contradiction x≤y x≰y
      res | sel≈ _   y≤x | sel≈ _   z≤y | yes _        | yes _        | sel≈ _   _   | sel₁ _   z≰x = contradiction (≤ᵣ-trans assoc z≤y y≤x) z≰x
      res | sel≈ x≤y _   | sel≈ y≤z _   | yes _        | yes _        | sel≈ _   _   | sel₂ x≰z _   = contradiction (≤ᵣ⇨≤ₗ comm (≤ᵣ-trans assoc (≤ₗ⇨≤ᵣ comm x≤y) (≤ₗ⇨≤ᵣ comm y≤z))) x≰z
      res | sel≈ _   _   | sel≈ _   _   | yes _        | yes _        | sel≈ _   _   | sel≈ _   _   with p ≤ₚ? q | p ≤ₚ? r
      res | sel≈ _   _   | sel≈ _   _   | yes _        | yes _        | sel≈ _   _   | sel≈ _   _   | yes _       | yes _      = ≈ⁱ-refl
      res | sel≈ _   _   | sel≈ _   _   | yes p≤q      | yes q≤r      | sel≈ _   _   | sel≈ _   _   | yes _       | no  p≰r    = contradiction (≤ₚ-trans p≤q q≤r) p≰r
      res | sel≈ _   _   | sel≈ _   _   | yes p≤q      | yes _        | sel≈ _   _   | sel≈ _   _   | no  p≰q     | _          = contradiction p≤q p≰q
      res | sel≈ _   _   | sel≈ _   _   | yes _        | no  _        = ≈ⁱ-refl
      res | sel≈ _   _   | sel≈ _   _   | no  _        | yes _        with ⊕-select x y | ⊕-select y z
      res | sel≈ _   y≤x | sel≈ _   _   | no  _        | yes _        | sel₁ _   y≰x | _            = contradiction y≤x y≰x
      res | sel≈ x≤y _   | sel≈ _   _   | no  _        | yes _        | sel₂ x≰y _   | _            = contradiction x≤y x≰y
      res | sel≈ _   _   | sel≈ _   z≤y | no  _        | yes _        | _            | sel₁ _   z≰y = contradiction z≤y z≰y
      res | sel≈ _   _   | sel≈ y≤z _   | no  _        | yes _        | _            | sel₂ y≰z _   = contradiction y≤z y≰z
      res | sel≈ _   _   | sel≈ _   _   | no  _        | yes _        | sel≈ _   _   | sel≈ _   _   with p ≤ₚ? q | q ≤ₚ? r
      res | sel≈ _   _   | sel≈ _   _   | no  p≰q      | yes _        | sel≈ _   _   | sel≈ _   _   | yes p≤q     | _          = contradiction p≤q p≰q
      res | sel≈ _   _   | sel≈ _   _   | no  _        | yes q≤r      | sel≈ _   _   | sel≈ _   _   | _           | no  q≰r    = contradiction q≤r q≰r
      res | sel≈ _   _   | sel≈ _   _   | no  _        | yes _        | sel≈ _   _   | sel≈ _   _   | no  _       | yes _      = ≈ⁱ-refl
      res | sel≈ _   _   | sel≈ _   _   | no  _        | no  _        with ⊕-select x z | ⊕-select y z
      res | sel≈ _   _   | sel≈ _   z≤y | no  _        | no  _        | _            | sel₁ _   z≰y = contradiction z≤y z≰y
      res | sel≈ _   _   | sel≈ y≤z _   | no  _        | no  _        | _            | sel₂ y≰z _   = contradiction y≤z y≰z
      res | sel≈ _   y≤x | sel≈ _   z≤y | no  _        | no  _        | sel₁ _   z≰x | sel≈ _   _   = contradiction (≤ᵣ-trans assoc z≤y y≤x) z≰x
      res | sel≈ x≤y _   | sel≈ y≤z _   | no  _        | no  _        | sel₂ x≰z _   | sel≈ _   _   = contradiction (≤ᵣ⇨≤ₗ comm (≤ᵣ-trans assoc (≤ₗ⇨≤ᵣ comm x≤y) (≤ₗ⇨≤ᵣ comm y≤z))) x≰z
      res | sel≈ _   _   | sel≈ _   _   | no  _        | no  _        | sel≈ _   _   | sel≈ _   _   with p ≤ₚ? r | q ≤ₚ? r
      res | sel≈ _   _   | sel≈ _   _   | no  _        | no  q≰r      | sel≈ _   _   | sel≈ _   _   | _           | yes q≤r    = contradiction q≤r q≰r
      res | sel≈ _   _   | sel≈ _   _   | no  _        | no  _        | sel≈ _   _   | sel≈ _   _   | no  _       | no  _      = ≈ⁱ-refl
      res | sel≈ _   _   | sel≈ _   _   | no  _        | no  _        | sel≈ _   _   | sel≈ _   _   | yes _       | no  _      with ≤ₚ-total p q
      res | sel≈ _   _   | sel≈ _   _   | no  p≰q      | no  _        | sel≈ _   _   | sel≈ _   _   | yes _       | no  _      | inj₁ p≤q = contradiction p≤q p≰q
      res | sel≈ _   _   | sel≈ _   _   | no  p≰q      | no  q≰r      | sel≈ _   _   | sel≈ _   _   | yes p≤r     | no  _      | inj₂ q≤p = contradiction (≤ₚ-trans q≤p p≤r) q≰r

    ----------------------
    -- Properties of ▷ⁱ --
    ----------------------

    ⊕ⁱ-almost-strictly-absorbs-▷ⁱ : (∀ s r → (s ▷ r) ⊕ r ≈ r) → ∀ s {r} → r ≉ⁱ inull → ((s ▷ⁱ r) ⊕ⁱ r ≈ⁱ r) × (r ≉ⁱ s ▷ⁱ r)
    ⊕ⁱ-almost-strictly-absorbs-▷ⁱ _   _       {inull}       r≉inull = contradiction inullEq r≉inull
    ⊕ⁱ-almost-strictly-absorbs-▷ⁱ abs (i , j) {iroute x []} _ with i ≟𝔽 j | (i , j) ∈? G
    ... | yes _   | _           = ≈ⁱ-refl , λ()
    ... | no  _   | no _        = ≈ⁱ-refl , λ()
    ... | no  i≢j | yes (v , _) with v ▷ x ≟ 0#
    ...   | yes _ = ≈ⁱ-refl , λ()
    ...   | no  _ with ⊕-select (v ▷ x) x
    ...     | sel₁ _ vx⊕x≉x = contradiction (abs v x) vx⊕x≉x
    ...     | sel₂ _ _      = ≈ⁱ-refl , λ{(irouteEq x≈vx ())}
    ...     | sel≈ _ _      with [ i ∺ j ∣ i≢j ] ≤ₚ? []
    ...       | yes ()
    ...       | no  _ = ≈ⁱ-refl , λ{(irouteEq x≈vx ())}
    ⊕ⁱ-almost-strictly-absorbs-▷ⁱ abs (i , j) {iroute x [ p ]} _  with j ≟𝔽 source p | i ∉? [ p ] | (i , j) ∈? G
    ... | no  _ | _           | _           = ≈ⁱ-refl , λ()
    ... | yes _ | no  _       | _           = ≈ⁱ-refl , λ()
    ... | yes _ | yes _       | no  _       = ≈ⁱ-refl , λ()
    ... | yes _ | yes [ i∉p ] | yes (v , _)  with v ▷ x ≟ 0#
    ...   | yes _ = ≈ⁱ-refl , λ()
    ...   | no  _ with ⊕-select (v ▷ x) x
    ...     | sel₁ _       vx⊕x≉x = contradiction (abs v x) vx⊕x≉x
    ...     | sel₂ vx⊕x≉vx _      = ≈ⁱ-refl , λ{(irouteEq _ [ p≈i∷p ]) → p≉i∷p p≈i∷p}
    ...     | sel≈ _       _      with [ i ∷ p ∣ i∉p ] ≤ₚ? [ p ]
    ...       | yes i∷p≤p = contradiction i∷p≤p i∷p≰p
    ...       | no  i∷p≰p = ≈ⁱ-refl , λ{(irouteEq _ [ p≈i∷p ]) → p≉i∷p p≈i∷p}


    -----------------
    -- Consistency --
    -----------------

    open RoutingProblem 𝓡𝓟ⁱ using (_≈ₘ_)
    
    𝑪? : Decidable 𝑪
    𝑪? inull = yes 𝒄-null
    𝑪? (iroute x p) with p ∈𝔾? G
    ...   | no  p∉G = no (𝒊-route-∉ x p∉G)
    ...   | yes p∈G with x ≟ weight p∈G
    ...     | no  x≉w[p] = no (𝒊-route-≉ p∈G x≉w[p])
    ...     | yes x≈w[p] = yes (𝒄-route p∈G x≈w[p])

    𝑪ₘ? : Decidable 𝑪ₘ
    𝑪ₘ? X = all? (λ i → all? (λ j → 𝑪? (X i j)))
    
    𝑪-cong : ∀ {x y} → 𝑪 x → x ≈ⁱ y → 𝑪 y
    𝑪-cong 𝒄-null               inullEq            = 𝒄-null
    𝑪-cong (𝒄-route p∈G x≈w[p]) (irouteEq x≈y p≈q) = 𝒄-route (∈𝔾-resp-≈ₚ p≈q p∈G) (≈-trans (≈-trans (≈-sym x≈y) x≈w[p]) (≈-reflexive (weight-cong _▷_ 1# p≈q p∈G (∈𝔾-resp-≈ₚ p≈q p∈G))))

    𝑪ₘ-cong : ∀ {X Y} → 𝑪ₘ X → X ≈ₘ Y → 𝑪ₘ Y
    𝑪ₘ-cong Xᶜ X≈Y i j = 𝑪-cong (Xᶜ i j) (X≈Y i j)

    𝑰ₘ-witness : ∀ {X} → 𝑰ₘ X → ∃₂ λ i j → 𝑰 (X i j)
    𝑰ₘ-witness {X} ¬Xᶜ with ¬∀⟶∃¬ n _ (λ i → all? (λ j → 𝑪? (X i j))) ¬Xᶜ
    ... | (i , ¬Xᵢᶜ) with ¬∀⟶∃¬ n _ (λ j → 𝑪? (X i j)) ¬Xᵢᶜ
    ...   | (j , ¬Xᵢⱼᶜ) = i , j , ¬Xᵢⱼᶜ
    

    ⊕ⁱ-pres-𝑪 : _⊕ⁱ_ ×-Preserves 𝑪
    ⊕ⁱ-pres-𝑪 {_}          {_}          𝒄-null               𝒄-null               = 𝒄-null
    ⊕ⁱ-pres-𝑪 {_}          {_}          𝒄-null               (𝒄-route q∈G y≈w[q]) = 𝒄-route q∈G y≈w[q]
    ⊕ⁱ-pres-𝑪 {_}          {_}          (𝒄-route p∈G x≈w[p]) 𝒄-null               = 𝒄-route p∈G x≈w[p]
    ⊕ⁱ-pres-𝑪 {iroute x p} {iroute y q} (𝒄-route p∈G x≈w[p]) (𝒄-route q∈G y≈w[q]) with ⊕-select x y
    ... | sel₁ _ _ = 𝒄-route p∈G x≈w[p]
    ... | sel₂ _ _ = 𝒄-route q∈G y≈w[q]
    ... | sel≈ _ _ with p ≤ₚ? q
    ...   | yes _ = 𝒄-route p∈G x≈w[p]
    ...   | no  _ = 𝒄-route q∈G y≈w[q]
  
    ▷ⁱ-pres-𝑪 : ∀ e {x} → 𝑪 x → 𝑪 (e ▷ⁱ x)
    ▷ⁱ-pres-𝑪 e       {_}           𝒄-null = 𝒄-null
    ▷ⁱ-pres-𝑪 (i , j) {iroute x []} (𝒄-route [] x≈1#) with i ≟𝔽 j | (i , j) ∈? G
    ... | yes _  | _               = 𝒄-null
    ... | no  _  | no  _           = 𝒄-null
    ... | no i≢j | yes (v , Gᵢⱼ≈v) with v ▷ x ≟ 0#
    ...   | yes _ = 𝒄-null
    ...   | no  _ = 𝒄-route [ (edge-∺ (v , Gᵢⱼ≈v)) ] (▷-cong v x≈1#)
    ▷ⁱ-pres-𝑪 (i , j) {iroute x [ p ]} (𝒄-route [ p∈G ] x≈w[p]) with j ≟𝔽 source p | i ∉? [ p ] | (i , j) ∈? G
    ... | no _     | _       | _           = 𝒄-null
    ... | yes _    | no  _   | _           = 𝒄-null
    ... | yes _    | yes _   | no _        = 𝒄-null
    ... | yes ≡-refl | yes [ i∉p ] | yes (v , Gᵢⱼ≡v) with v ▷ x ≟ 0#
    ...   | yes _ = 𝒄-null
    ...   | no  _ = 𝒄-route [ edge-∷ (v , Gᵢⱼ≡v) p∈G ] (▷-cong v x≈w[p])
  
    -----------
    -- Other --
    -----------
    
    size-cong : ∀ {r s} → r ≈ⁱ s → size r ≡ size s
    size-cong inullEq          = ≡-refl
    size-cong (irouteEq _ p≈q) = p≈q⇒|p|≡|q| p≈q

    size<n : ∀ {n'} → n ≡ suc n' → ∀ r → size r < n
    size<n ≡-refl inull        = s≤s z≤n
    size<n ≡-refl (iroute _ p) = length<n p
    
    ▷ⁱ-size : ∀ e {x} y → x ≉ⁱ inull → x ≈ⁱ e ▷ⁱ y → size x ≡ suc (size y)
    ▷ⁱ-size _       {inull}      _             null≉null x≈e▷y   = contradiction inullEq null≉null
    ▷ⁱ-size _       {iroute _ _} inull         x≉inull   x≈inull = contradiction x≈inull x≉inull
    ▷ⁱ-size (i , j) {iroute x p} (iroute y []) x≉inull   x≈e▷y   with i ≟𝔽 j | (i , j) ∈? G
    ... | yes _  | _           = contradiction x≈e▷y x≉inull
    ... | no  _  | no  _       = contradiction x≈e▷y x≉inull
    ... | no i≢j | yes (v , _) with v ▷ y ≟ 0#
    ...   | yes _ = contradiction x≈e▷y x≉inull
    ...   | no  _ = size-cong x≈e▷y
    ▷ⁱ-size (i , j) {iroute x p} (iroute y [ q ]) x≉inull x≈e▷y with j ≟𝔽 source q | i ∉? [ q ] | (i , j) ∈? G
    ... | no  _ | _           | _           = contradiction x≈e▷y x≉inull
    ... | yes _ | no  _       | _           = contradiction x≈e▷y x≉inull
    ... | yes _ | yes _       | no _        = contradiction x≈e▷y x≉inull
    ... | yes _ | yes [ i∉p ] | yes (v , _) with v ▷ y ≟ 0#
    ...   | yes _ = contradiction x≈e▷y x≉inull
    ...   | no  _ = size-cong x≈e▷y


