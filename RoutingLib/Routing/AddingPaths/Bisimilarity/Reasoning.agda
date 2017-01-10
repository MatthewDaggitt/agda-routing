
open import Data.Nat using (ℕ; suc)
open import Relation.Binary using (IsDecEquivalence)

open import RoutingLib.Routing.Definitions
open import RoutingLib.Data.Graph using (Graph)
open import RoutingLib.Data.Graph.EPath.Properties using (≈ₚ-trans; ≈ₚ-sym)
open import RoutingLib.Algebra.FunctionProperties using (Selective)


module RoutingLib.Routing.AddingPaths.Bisimilarity.Reasoning
  {a b ℓ} (ra : RoutingAlgebra a b ℓ) 
  (⊕-sel : Selective (RoutingAlgebra._≈_ ra) (RoutingAlgebra._⊕_ ra))
  (one : (RoutingAlgebra.Route ra))
  {n : ℕ}
  (G : Graph (RoutingAlgebra.Step ra) n)
  where

  open RoutingAlgebra ra

  open import RoutingLib.Routing.AddingPaths.Bisimilarity ra ⊕-sel one G
  open import RoutingLib.Routing.AddingPaths.Consistent ra ⊕-sel one G using (_≈ᶜ_; ≈ᶜ-sym; cnullEq; crouteEq)
  open import RoutingLib.Routing.AddingPaths.Inconsistent ra ⊕-sel one G using (_≈ⁱ_; ≈ⁱ-refl; ≈ⁱ-trans; inullEq; irouteEq)


  abstract

    -----------
    -- ≃ & ≈ --
    -----------

    cic-trans : ∀ {x y z} → x ≃ y → z ≃ y → x ≈ᶜ z
    cic-trans nullEq            nullEq            = cnullEq
    cic-trans (routeEq x≈y p≈q) (routeEq z≈y r≈q) = crouteEq (trans x≈y (sym z≈y)) (≈ₚ-trans p≈q (≈ₚ-sym r≈q))

    cci-trans : ∀ {x y z} → x ≈ᶜ y → y ≃ z → x ≃ z
    cci-trans cnullEq            nullEq            = nullEq
    cci-trans (crouteEq x≈y p≈q) (routeEq y≈z q≈r) = routeEq (trans x≈y y≈z) (≈ₚ-trans p≈q q≈r)

    cii-trans : ∀ {x y z} → x ≃ y → y ≈ⁱ z → x ≃ z
    cii-trans nullEq            inullEq            = nullEq
    cii-trans (routeEq x≈y p≈q) (irouteEq y≈z q≈r) = routeEq (trans x≈y y≈z) (≈ₚ-trans p≈q q≈r)

    ici-trans : ∀ {x y z} → x ≃ y → x ≃ z → y ≈ⁱ z
    ici-trans nullEq            nullEq             = inullEq
    ici-trans (routeEq x≈y p≈q) (routeEq x≈z p≈r)  = irouteEq (trans (sym x≈y) x≈z) (≈ₚ-trans (≈ₚ-sym p≈q) p≈r)


    infix  3 _∎
    infixr 2 _≈ᶜ⟨_⟩_ _≈ⁱ⟨_⟩_ _≃ⁱᶜ⟨_⟩_ _≃ᶜⁱ⟨_⟩_
    infix  1 begin_

    begin_ : ∀{x y} → x ≈ⁱ y → x ≈ⁱ y
    begin_ x≈y = x≈y

    _≈ⁱ⟨_⟩_ : ∀ x {y z} → x ≈ⁱ y → y ≈ⁱ z → x ≈ⁱ z 
    _ ≈ⁱ⟨ x≈y ⟩ y≈z = ≈ⁱ-trans x≈y y≈z

    _≈ᶜ⟨_⟩_ : ∀ x {y z} → x ≈ᶜ y → y ≃ z → x ≃ z
    _ ≈ᶜ⟨ x≈y ⟩ y≃z = cci-trans x≈y y≃z

    _≃ⁱᶜ⟨_⟩_ : ∀ x {y z} → x ≃ y → y ≈ⁱ z → x ≃ z
    _ ≃ⁱᶜ⟨ x≃y ⟩ y≈z = cii-trans x≃y y≈z

    _≃ᶜⁱ⟨_⟩_ : ∀ {x} y {z} → x ≃ y → x ≃ z → y ≈ⁱ z
    _ ≃ᶜⁱ⟨ x≃y ⟩ x≃z = ici-trans x≃y x≃z

    _∎ : ∀ x → x ≈ⁱ x
    _ ∎ = ≈ⁱ-refl
