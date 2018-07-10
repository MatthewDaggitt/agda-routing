# Agda-routing

This library reasons about iterative asynchronous processes and network routing problems.
It is organised in the same manner as the Agda standard library and contains extensions of
several of the Agda standard library modules. The core contributions of this library
can be found in the `RoutingLib.Asynchronous` and `RoutingLib.Routing` directories.

## Asynchronous reasoning

* `RoutingLib.Asynchronous` contains a record type encoding parallelisations of iterative algorithms.

* `RoutingLib.Asynchronous.Schedule` contains a formalisation of asynchronous schedules.

* `RoutingLib.Asynchronous.Convergence.Conditions` contains various conditions that are sufficient
  to guarantee convergence.

* `RoutingLib.Asynchronous.Convergence.Theorems` contains the top level proofs that the conditions
  are sufficient.

* `RoutingLib.Asynchronous.Convergence.Proofs` contains the proofs of these theorems from
  `Parallel Asynchronous Algorithms for Discrete Data` by `A. Uresin` & `M. Dubois` and
  `Asynchronous iterations in ultrametric spaces` by `A. J. T. Gurney`.

To use these results you should construct your synchronous iteration, show that it fulfils one of the
conditions in `Convergence.Conditions` and then use the relevant theorem in `Convergence.Theorems`.

## Routing proofs

The author's main use for this library has been to apply this work to internet routing protocols based
on the Distributed Bellman Ford (DBF) algorithm.

* `RoutingLib.Routing.BellmanFord` contains an implementation of generalised distributed Bellman Ford-based routing algorithms.

* `RoutingLib.Routing.BellmanFord.Theorems` contains various proofs about distance-vector and path-vector protocols.

* `RoutingLib.Routing.BellmanFord.Models.BGPLite` shows how the work may be used to create a safe-by-design protocol.

## Requirements

Requires Agda 2.5.4 and Standard Library 0.16

## Postulates

Currently there are no postulates in the library.

## Related work

* `Üresin, A`., `Dubois, M.` _Parallel asynchronous algorithms for discrete data_. J. ACM
37(3) (Jul 1990)

* `Gurney, A.J.T.` _Asynchronous iterations in ultrametric spaces_ (2017),
https://arxiv.org/abs/1701.07434

## Resulting publications

* `Daggitt, M.L.`, `Gurney, A.J.T`., `Griffin, T.G.`: _Asynchronous convergence of policy-
rich distributed bellman-ford routing protocols_ SIGCOMM (2018)

* `Daggitt, M.L`, `Griffin, T.G.` _Rate of convergence
of increasing path-vector routing protocols_ (2018). Under submission.

* `Zmigrod, R. `, `Daggitt, M.L.`, `Griffin, T. G.` _An
Agda Formalization of Üresin & Dubois’ Asynchronous Fixed-Point
Theory_ ITP (2018).
