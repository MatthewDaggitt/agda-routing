# Agda-routing for ITP 2018

This library reasons about iterative asynchronous processes and network routing problems. 
It is organised in the same manner as the Agda standard library and contains extensions of 
several of the Agda standard library modules. The core contributions of this library 
can be found in the `RoutingLib.Asynchronous` and `RoutingLib.Routing` directories.

This is the frozen version of the library accompanying the paper
`An Agda Formalization of Üresin & Dubois' Asynchronous Fixed-Point Theory`
by `Ran Zmigrod`, `Matthew L. Daggitt` and `Timothy G Griffin` in `ITP 2018`. 
The latest version of the library can be found on the 
[master](https://github.com/MatthewDaggitt/agda-routing/tree/master) branch in this
repository.

# Asynchronous reasoning

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

# Routing feautres

The author's main use for this library has been to apply this work to internet routing protocols based
on the Distributed Bellman Ford (DBF) algorithm.

- `RoutingLib.Routing.BellmanFord` contains an implementation of generalised distributed Bellman Ford-based routing algorithms.
	
- `RoutingLib.Routing.BellmanFord.Theorems` contains various proofs about distance-vector and path-vector protocols.

## Requirements

Requires Agda 2.5.4 and Standard Library 0.16

## Postulates

Currently the only postulates are in `Data.List.Sorting.Mergesort`. At some point I plan to get around to writing an implementation, 
but hopefully in the meantime it is obvious that they are fairly inoffensive.
