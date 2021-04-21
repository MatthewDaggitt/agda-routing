
open import Data.Fin
open import Data.Nat
open import Data.Fin.Subset
open import Data.Product using (_×_)

module RoutingLib.Routing.Basics.Node
  (n : ℕ) -- The size of the network
  where

--------------------------------------------------------------------------------
-- Definitions

-- The nodes that participate in a routing computation are simply a finite set
-- of numbers from 1 to n.

Node : Set
Node = Fin n

-- The set of nodes that are actually participating at a particular time is
-- simply a subset of the nodes

Participants : Set
Participants = Subset n
