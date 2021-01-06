--------------------------------------------------------------------------------
-- Agda routing library
--
-- This module contains the definition of the algebra underlying a distance
-- vector protocol that solves the shortest-widest paths problem, i.e. tries to
-- choose the highest bandwidth path and breaks ties based on path length.
--------------------------------------------------------------------------------

open import Level using (0ℓ)

open import RoutingLib.Routing.Algebra
open import RoutingLib.Routing.Algebra.Construct.Lex
  as Lex using (Lex)
open import RoutingLib.Routing.Algebra.Construct.AddPaths
  as AddPaths using (AddPaths)
  
module RoutingLib.Routing.Protocols.ShortestWidestPaths where

open import RoutingLib.Routing.Protocols.ShortestPaths as Shortest using (Aˢʰᵒʳᵗᵉˢᵗ)
open import RoutingLib.Routing.Protocols.WidestPaths   as Widest   using (Aʷⁱᵈᵉˢᵗ)

--------------------------------------------------------------------------------
-- Distance vector algebra

Aˢʷ : RawRoutingAlgebra 0ℓ 0ℓ 0ℓ
Aˢʷ = Lex Aʷⁱᵈᵉˢᵗ Aˢʰᵒʳᵗᵉˢᵗ

Aˢʷ-isRoutingAlgebra : IsRoutingAlgebra Aˢʷ
Aˢʷ-isRoutingAlgebra = Lex.isRoutingAlgebra Aʷⁱᵈᵉˢᵗ Aˢʰᵒʳᵗᵉˢᵗ Widest.isRoutingAlgebra Shortest.isRoutingAlgebra

--------------------------------------------------------------------------------
-- Path vector algebra

Aˢʷᵖ : RawRoutingAlgebra 0ℓ 0ℓ 0ℓ
Aˢʷᵖ = AddPaths Aˢʷ

Aˢʷᵖ-isRoutingAlgebra : IsRoutingAlgebra Aˢʷᵖ
Aˢʷᵖ-isRoutingAlgebra = AddPaths.isRoutingAlgebra Aˢʷ Aˢʷ-isRoutingAlgebra

Aˢʷᵖ-isPathAlgebra : IsPathAlgebra Aˢʷᵖ
Aˢʷᵖ-isPathAlgebra = AddPaths.isPathAlgebra Aˢʷ
