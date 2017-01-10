
open import Data.Nat using (ℕ; suc)

open import RoutingLib.Data.Graph
open import RoutingLib.Data.Graph.Subgraph
open import RoutingLib.Routing.Definitions using (RoutingAlgebra)
open import RoutingLib.Algebra.FunctionProperties using (Selective)


module RoutingLib.Routing.AddingPaths.Consistent.SubgraphConversion
  {a b ℓ} (ra : RoutingAlgebra a b ℓ) 
  (⊕-sel : Selective (RoutingAlgebra._≈_ ra) (RoutingAlgebra._⊕_ ra))
  (one : (RoutingAlgebra.Route ra))
  where

  open RoutingAlgebra ra
  open import RoutingLib.Routing.AddingPaths.Consistent ra ⊕-sel one


  -- Up conversion

  ↑convertCRoute : ∀ {n-2} (G : Graph Step (suc (suc n-2))) i → CRoute (G / i) → CRoute G
  ↑convertCRoute G i cnull = cnull
  ↑convertCRoute G i (croute x p x≈w[p]) = croute x (↑convert G i p) (trans x≈w[p] (reflexive (↑convert-weight _▷_ one G i p)))

  ↑convertCRoute-cong : ∀ {n-2} (G : Graph Step (suc (suc n-2))) i {x y} → _≈ᶜ_ (G / i) x y → _≈ᶜ_ G (↑convertCRoute G i x) (↑convertCRoute G i y)
  ↑convertCRoute-cong G i cnullEq = cnullEq
  ↑convertCRoute-cong G i (crouteEq x≈y p≈q) = crouteEq x≈y (↑convert-cong G i p≈q)
