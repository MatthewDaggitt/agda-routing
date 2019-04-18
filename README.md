Agda-routing for Matthew Daggitt's PhD thesis
=============================================

This library reasons about iterative asynchronous processes and network routing
problems. It is organised in the same manner as the Agda standard library and 
contains extensions of several of the Agda standard library modules. The core 
contributions of this library can be found in the `RoutingLib.Iteration` and 
`RoutingLib.Routing` directories.

This is the frozen version of the library accompanying _An Algebraic Perspective
on the Convergence of Vector-Based Routing Protocols_ by Matthew L. Daggitt, 
submitted for his PhD thesis at the Department of Computer Science and 
Technology, University Of Cambridge, 2019. The latest version of the library
can be found on the [master](https://github.com/MatthewDaggitt/agda-routing) branch of this repository.

Requires: Agda 2.6.0 and Standard Library 1.0

Below is a guide that helps users match up the content of the thesis with their associated
formalisation in Agda.

## Chapter 3 - Asynchronous iterative algorithms

A formalisation of the pre-existing theory of static asynchronous iterative
algorithms can be found in the directory `RoutingLib.Iteration.Asynchronous.Static`
and is organised as follows:

* Static schedules:
[RoutingLib.Iteration.Asynchronous.Static.Schedule](https://github.com/MatthewDaggitt/agda-routing/blob/thesis/RoutingLib/Iteration/Asynchronous/Static/Schedule.agda)

* Static pseudoperiods:
[RoutingLib.Iteration.Asynchronous.Static.Schedule.Pseudoperiod](https://github.com/MatthewDaggitt/agda-routing/blob/thesis/RoutingLib/Iteration/Asynchronous/Static/Schedule/Pseudoperiod.agda)

* The static asynchronous iteration state function δ, and what it means for it to be correct:
[RoutingLib.Iteration.Asynchronous.Static](https://github.com/MatthewDaggitt/agda-routing/blob/thesis/RoutingLib/Iteration/Asynchronous/Static.agda)

* Conditions sufficient for convergence (ACO, AMCO etc.):
[RoutingLib.Iteration.Asynchronous.Static.Convergence.Conditions](https://github.com/MatthewDaggitt/agda-routing/blob/thesis/RoutingLib/Iteration/Asynchronous/Static/Convergence/Conditions.agda)

* Proof that our relaxation of the ACO conditions are equivalent to that of Uresin & Dubois:
[RoutingLib.Iteration.Asynchronous.Static.Convergence.RelaxACO](https://github.com/MatthewDaggitt/agda-routing/blob/thesis/RoutingLib/Iteration/Asynchronous/Static/Convergence/RelaxACO.agda)

A formalisation of the new theory of dynamic asynchronous iterations
can be found in the directory `RoutingLib.Iteration.Asynchronous.Dynamic` 
and is organised as follows:

* Dynamic schedules:
[RoutingLib.Iteration.Asynchronous.Dynamic.Schedule](https://github.com/MatthewDaggitt/agda-routing/blob/thesis/RoutingLib/Iteration/Asynchronous/Dynamic/Schedule.agda)

* Dynamic pseudoperiods:
[RoutingLib.Iteration.Asynchronous.Dynamic.Schedule.Pseudoperiod](https://github.com/MatthewDaggitt/agda-routing/blob/thesis/RoutingLib/Iteration/Asynchronous/Dynamic/Schedule/Pseudoperiod.agda)

* Dynamic asynchronous iteration and what it means for it to be correct:
[RoutingLib.Iteration.Asynchronous.Dynamic](https://github.com/MatthewDaggitt/agda-routing/blob/thesis/RoutingLib/Iteration/Asynchronous/Dynamic.agda)

* Conditions sufficient for convergence (dynamic ACO, dynamic AMCO etc.):
[RoutingLib.Iteration.Asynchronous.Dynamic.Convergence.Conditions](https://github.com/MatthewDaggitt/agda-routing/blob/thesis/RoutingLib/Iteration/Asynchronous/Dynamic/Convergence/Conditions.agda)

* Proof of Theorem 1 that ACO implies convergence:
[RoutingLib.Iteration.Asynchronous.Dynamic.Convergence.ACOImpliesConvergent](https://github.com/MatthewDaggitt/agda-routing/blob/thesis/RoutingLib/Iteration/Asynchronous/Dynamic/Convergence/ACOImpliesConvergent.agda)

* Proof of Theorem 3 that F is a dynamic AMCO implies F is a dynamic ACO is found in:
[RoutingLib.Iteration.Asynchronous.Dynamic.Convergence.AMCOImpliesACO](https://github.com/MatthewDaggitt/agda-routing/blob/thesis/RoutingLib/Iteration/Asynchronous/Dynamic/Convergence/AMCOImpliesACO.agda)

* Public facing interface that should be used to prove new convergence results:
[RoutingLib.Iteration.Asynchronous.Dynamic.Convergence](https://github.com/MatthewDaggitt/agda-routing/blob/thesis/RoutingLib/Iteration/Asynchronous/Dynamic/Convergence.agda)

## Chapter 4 - An algebraic model for vector-based protocols

* The definition of routing algebras and path algebras as well as the definition of properties
like distributive, strictly increasing, finite etc. can be found in:
[RoutingLib.Routing.Algebra](https://github.com/MatthewDaggitt/agda-routing/blob/thesis/RoutingLib/Routing/Algebra.agda)

* The basic definitions of next-hop routing, including the definition of the network,
adjacency matrices, routing states etc. can be found in:
[RoutingLib.Routing](https://github.com/MatthewDaggitt/agda-routing/blob/thesis/RoutingLib/Routing.agda)

* The synchronous model for an abstract vector-based routing protocol can be found in:
[RoutingLib.Routing.VectorBased.Synchronous](https://github.com/MatthewDaggitt/agda-routing/blob/thesis/RoutingLib/Routing/VectorBased/Synchronous.agda)

* The asynchronous model for an abstract vector-based routing protocol can be found in:
[RoutingLib.Routing.VectorBased.Synchronous](https://github.com/MatthewDaggitt/agda-routing/blob/thesis/RoutingLib/Routing/VectorBased/Asynchronous.agda)

* The code for ℙ(∙), the generic method of constructing path algebras from routing algebras,
is in:
[RoutingLib.Routing.Algebra.Construct.AddPaths](https://github.com/MatthewDaggitt/agda-routing/blob/thesis/RoutingLib/Routing/Algebra/Construct/AddPaths.agda)

* Some examples of basic routing algebras can be found in:
[RoutingLib.Routing.Protocols.DistanceVector.ShortestPaths](https://github.com/MatthewDaggitt/agda-routing/blob/thesis/RoutingLib/Routing/Protocols/DistanceVector/ShortestPaths.agda)
[RoutingLib.Routing.Protocols.DistanceVector.WidestPaths](https://github.com/MatthewDaggitt/agda-routing/blob/thesis/RoutingLib/Routing/Protocols/DistanceVector/WidestPaths.agda)
[RoutingLib.Routing.Protocols.DistanceVector.ShortestWidestPaths](https://github.com/MatthewDaggitt/agda-routing/blob/thesis/RoutingLib/Routing/Protocols/DistanceVector/ShortestWidestPaths.agda)

## Chapter 5 - Convergence

The proof of convergence of finite, strictly increasing distance-vector protocols is 
organised as follows:

* The definitions of the height function and associated metrics are in:
[RoutingLib.Routing.VectorBased.Asynchronous.DistanceVector.Convergence.Metrics](https://github.com/MatthewDaggitt/agda-routing/blob/thesis/RoutingLib/Routing/VectorBased/Asynchronous/DistanceVector/Convergence/Metrics.agda)

* The properties of the height function and associated metrics are in:
[RoutingLib.Routing.VectorBased.Asynchronous.DistanceVector.Convergence.Properties](https://github.com/MatthewDaggitt/agda-routing/blob/thesis/RoutingLib/Routing/VectorBased/Asynchronous/DistanceVector/Convergence/Properties.agda)

* The proof that `F` is strictly contracting over 
[RoutingLib.Routing.VectorBased.Asynchronous.DistanceVector.Convergence.StrictlyContracting](https://github.com/MatthewDaggitt/agda-routing/blob/thesis/RoutingLib/Routing/VectorBased/Asynchronous/DistanceVector/Convergence/StrictlyContracting.agda)

The proof of convergence of increasing path-vector protocols is organised as follows:

* The definitions of the height function and associated metrics are in:
[RoutingLib.Routing.VectorBased.Asynchronous.PathVector.Convergence.Metrics](https://github.com/MatthewDaggitt/agda-routing/blob/thesis/RoutingLib/Routing/VectorBased/Asynchronous/PathVector/Convergence/Metrics.agda)

* The properties of the height function and associated metrics are in:
[RoutingLib.Routing.VectorBased.Asynchronous.PathVector.Convergence.Properties](https://github.com/MatthewDaggitt/agda-routing/blob/thesis/RoutingLib/Routing/VectorBased/Asynchronous/PathVector/Convergence/Properties.agda)

* The proof that `F` is strictly contracting over 
[RoutingLib.Routing.VectorBased.Asynchronous.PathVector.Convergence.StrictlyContracting](https://github.com/MatthewDaggitt/agda-routing/blob/thesis/RoutingLib/Routing/VectorBased/Asynchronous/PathVector/Convergence/StrictlyContracting.agda)

A summary of all the convergence results can be found in:
[RoutingLib.Routing.VectorBased.Asynchronous.Results](https://github.com/MatthewDaggitt/agda-routing/blob/thesis/RoutingLib/Routing/VectorBased/Asynchronous/Results.agda)

## Chapter 6 - Rate of convergence

Note that, as discussed in the thesis, the Θ(n²) convergence time for 
the Qₙ gadgets is the only major proof not formalised in Agda. This is because:
  
  1. it is time consuming to formally reason about the entire execution trace of
  an abstract family of graphs.
  
  2. being a lower bound there are less severe practical consequences if it turns
  out to be incorrect.
  
  3. execution traces that exhibit convincing quadratic behaviour have been generated
  using Python scripts.
  
The proof of the Ω(n²) bound on convergence in the worst case is laid out as follows:

* Definition and properties of the set of fixed/converged/real nodes.
[RoutingLib.Routing.VectorBased.Synchronous.PathVector.RateOfConvergence.Step1_NodeSets.agda](https://github.com/MatthewDaggitt/agda-routing/blob/thesis/RoutingLib/Routing/VectorBased/Synchronous/PathVector/RateOfConvergence/Step1_NodeSets.agda)

* Identification of the converged subtree and the minimal edge out of it.
[RoutingLib.Routing.VectorBased.Synchronous.PathVector.RateOfConvergence.Step2_ConvergedSubtree.agda](https://github.com/MatthewDaggitt/agda-routing/blob/thesis/RoutingLib/Routing/VectorBased/Synchronous/PathVector/RateOfConvergence/Step2_ConvergedSubtree.agda)

* Definition and properties of the set of dangerous nodes.
[RoutingLib.Routing.VectorBased.Synchronous.PathVector.RateOfConvergence.Step3_DangerousNodes.agda](https://github.com/MatthewDaggitt/agda-routing/blob/thesis/RoutingLib/Routing/VectorBased/Synchronous/PathVector/RateOfConvergence/Step3_DangerousNodes.agda)

* The main inductive step of the argument.
[RoutingLib.Routing.VectorBased.Synchronous.PathVector.RateOfConvergence.Step4_InductiveStep.agda](https://github.com/MatthewDaggitt/agda-routing/blob/thesis/RoutingLib/Routing/VectorBased/Synchronous/PathVector/RateOfConvergence/Step4_InductiveStep.agda)

* The full inductive argument.
[RoutingLib.Routing.VectorBased.Synchronous.PathVector.RateOfConvergence.Step5_Proof.agda](https://github.com/MatthewDaggitt/agda-routing/blob/thesis/RoutingLib/Routing/VectorBased/Synchronous/PathVector/RateOfConvergence/Step5_Proof.agda)

## Chapter 7 - Practicalities

* Definition of comparability:
[RoutingLib.Routing.Algebra.Comparable](https://github.com/MatthewDaggitt/agda-routing/blob/thesis/RoutingLib/Routing/Algebra/Comparable.agda)

* Definition of similarity and proof that it preserves convergence:
[RoutingLib.Routing.Algebra.Simulation](https://github.com/MatthewDaggitt/agda-routing/blob/thesis/RoutingLib/Routing/Algebra/Simulation.agda)

* Path inflation and deflation functions can be found in:
[RoutingLib.Data.Path.Uncertified](https://github.com/MatthewDaggitt/agda-routing/blob/thesis/RoutingLib/Data/Path/Uncertified.agda)

## Chapter 8 - Agda: proofs and protocols

* Definition of the algebra `BGPLite` based on a fragment BGP:
[RoutingLib.Routing.Protocols.PathVector.BGPLite.Main](https://github.com/MatthewDaggitt/agda-routing/blob/thesis/RoutingLib/Routing/Protocols/PathVector/BGPLite/Main.agda)

* Definition of a algebra `BGPLite-sim` that is similar to `BGPLite` yet has better algebraic properties:
[RoutingLib.Routing.Protocols.PathVector.BGPLite.Simulation](https://github.com/MatthewDaggitt/agda-routing/blob/thesis/RoutingLib/Routing/Protocols/PathVector/BGPLite/Simulation.agda)

* Proof that `BGPLite-sim` i) simulates `BGPLite` and ii) convergent:
[RoutingLib.Routing.Protocols.PathVector.BGPLite.Simulation.Properties](https://github.com/MatthewDaggitt/agda-routing/blob/thesis/RoutingLib/Routing/Protocols/PathVector/BGPLite/Simulation/Properties.agda)

* Proof that `BGPLite` is convergent:
[RoutingLib.Routing.Protocols.PathVector.BGPLite.Simulation.Properties](https://github.com/MatthewDaggitt/agda-routing/blob/thesis/RoutingLib/Routing/Protocols/PathVector/BGPLite/Main/Properties.agda)

## Related work

[1] `Üresin, A`., `Dubois, M.` 
_Parallel asynchronous algorithms for discrete  data_. Journal of the ACM 37(3) (1990)

[2] `Gurney, A.J.T.` 
_Asynchronous iterations in ultrametric spaces_ (2017),https://arxiv.org/abs/1701.07434

## Resulting publications

[3] `Daggitt, M.L.`, `Gurney, A.J.T`., `Griffin, T.G.`
_Asynchronous convergence of policy-rich distributed bellman-ford routing protocols_, SIGCOMM (2018)

[4] `Daggitt, M.L`, `Griffin, T.G.` 
_Rate of convergence of increasing path-vector routing protocols_, ICNP (2018)

[5] `Zmigrod, R. `, `Daggitt, M.L.`, `Griffin, T. G.` 
_An Agda Formalization of Üresin & Dubois’ Asynchronous Fixed-Point Theory_, ITP (2018).
