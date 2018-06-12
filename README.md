# agda-routing

An Agda library for reasoning about asynchronous processes and network routing problems. The library is laid out similarly to the Agda standard library and contains extensions of several of the Agda standard library modules. 

The core contributions of this library can be found in the `Asynchronous` and `Routing` directories.

- `RoutingLib.Asynchronous` contains the formalisation of Uresin & Dubois of asynchronous processes.
	
- `RoutingLib.Asynchronous.Theorems` contains various very general results about the convergence of asynchronous processes.

- `RoutingLib.Asynchronous.Propositions` contains various sufficient conditions that relate to the theorems above.
	
- `RoutingLib.Routing.BellmanFord` contains an implementation of generalised distributed Bellman Ford-based routing algorithms.
	
- `RoutingLib.Routing.BellmanFord.Theorems` contains various proofs about distance-vector and path-vector protocols.
	
- `RoutingLib.Asynchronous.Applications` contains a proof that a solution to the all-pairs shortest path problem converges asynchronously.

## Requirements

Requires Agda 2.5.4 and Standard Library 0.16

## Postulates

Currently the only postulates are in `Data.List.Sorting.Mergesort`. At some point I plan to get around to writing an implementation, but hopefully in the meantime it is obvious that they are fairly inoffensive.
