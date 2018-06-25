# Agda-routing for ITP 2018

This Agda library reasons about asynchronous processes and network routing problems. 
It is laid out similarly to the Agda standard library and contains extensions of 
several of the Agda standard library modules. The core contributions of this library 
can be found in the `RoutingLib.Asynchronous` and `RoutingLib.Routing` directories.

This is the frozen version of the library accompanying the paper
`An Agda Formalization of Üresin & Dubois' Asynchronous Fixed-Point Theory`
by `Ran Zmigrod`, `Matthew L. Daggitt` and `Timothy G Griffin` in `ITP 2018`. 
The latest version of the library can be found on the `master` branch in this
repository.

# Asynchronous reasoning

- `RoutingLib.Asynchronous` contains the formalisation of Uresin & Dubois of asynchronous processes.
	
- `RoutingLib.Asynchronous.Theorems` contains various very general results about the convergence of asynchronous processes.

- `RoutingLib.Asynchronous.Propositions` contains various sufficient conditions that relate to the theorems above.

# Routing feautres

- `RoutingLib.Routing.BellmanFord` contains an implementation of generalised distributed Bellman Ford-based routing algorithms.
	
- `RoutingLib.Routing.BellmanFord.Theorems` contains various proofs about distance-vector and path-vector protocols.
	
- `RoutingLib.Asynchronous.Applications` contains a proof that a solution to the all-pairs shortest path problem converges asynchronously.

## Requirements

Requires Agda 2.5.4 and Standard Library 0.16

## Postulates

Currently the only postulates are in `Data.List.Sorting.Mergesort`. At some point I plan to get around to writing an implementation, but hopefully in the meantime it is obvious that they are fairly inoffensive.
