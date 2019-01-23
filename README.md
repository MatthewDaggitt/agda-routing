# Agda-routing

This library reasons about iterative asynchronous processes and network routing problems.
It is organised in the same manner as the Agda standard library and contains extensions of
several of the Agda standard library modules. The core contributions of this library
can be found in the `RoutingLib.Iteration` and `RoutingLib.Routing` directories. The
rest of the library contains various stuff that should probably be pushed to the standard
library at some point, and is layed out correspondingly.

## Iterative algorithms

* `RoutingLib.Iteration.Asynchronous.(Static/Dynamic)` contains a record type encoding
  parallelisations of dynamic and static iterative algorithms.

* `RoutingLib.Iteration.Asynchronous.(Static/Dynamic).Schedule` contains a formalisation of
  schedules for static and dynamic asynchronous iterations.

* `RoutingLib.Iteration.Asynchronous.(Static/Dynamic).Convergence` contains theorems
  about the properties required for convergence.

* `RoutingLib.Iteration.Asynchronous.Dynamic.Convergence.ACOToSafe` contains a generalised
  version of Uresin \& Dubois's proof [1] that the (dynamic) ACO conditions implies the iteration
  is convergent.

* `RoutingLib.Iteration.Asynchronous.Dynamic.Convergence.UltrametricToACO` contains a
  generalised version of Gurney's proof [2] that the (dynamic) ACO conditions implies the iteration
  is convergent.

## Routing proofs

The author's main use for this library has been to apply this work to internet routing protocols based
on the Distributed Bellman Ford (DBF) algorithm.

* `RoutingLib.Routing` contains various concepts used in next-hop routing.

* `RoutingLib.Routing.Algebra` contains the definition of `RoutingAlgebra`s and `PathAlgebra`s. These
  are used to represent a generic routing problem.

* `RoutingLib.Routing.VectorBased.Asynchronous` contains a general model for an asynchronously
  implemented vector-based protocol. The model is agnostic to whether it the protocol is a distance-vector
  protocol or a path-vector protocol.

* `RoutingLib.Routing.VectorBased.Asynchronous.Results` contains various convergence theorems
  about distance-vector and path-vector protocols.

* `RoutingLib.Routing.Protocols.BGPLite` shwos how the work may be used to create a
  safe-by-design protocol that contains many of the features of BGP including path inflation,
  communities, conditional policy and local preferences.

## Requirements

Requires Agda 2.5.4 and Standard Library 0.17

## Postulates

Currently there are no postulates in the library.

## Related work

[1] `Üresin, A`., `Dubois, M.` _Parallel asynchronous algorithms for discrete data_. J. ACM
37(3) (Jul 1990)

[2] `Gurney, A.J.T.` _Asynchronous iterations in ultrametric spaces_ (2017),
https://arxiv.org/abs/1701.07434

## Resulting publications

* `Daggitt, M.L.`, `Gurney, A.J.T`., `Griffin, T.G.`: _Asynchronous convergence of policy-
rich distributed bellman-ford routing protocols_ SIGCOMM (2018)

* `Daggitt, M.L`, `Griffin, T.G.` _Rate of convergence
of increasing path-vector routing protocols_ ICNP (2018)

* `Zmigrod, R. `, `Daggitt, M.L.`, `Griffin, T. G.` _An
Agda Formalization of Üresin & Dubois’ Asynchronous Fixed-Point
Theory_ ITP (2018).
