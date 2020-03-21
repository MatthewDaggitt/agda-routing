# Agda-routing for JAR 2019

This library reasons about iterative asynchronous processes and network routing problems. It is organised in the same manner as the Agda standard library and contains extensions of several of the Agda standard library modules. The core contributions of this library can be found in the `RoutingLib.Iteration` and `RoutingLib.Routing` directories.

This is the frozen version of the library accompanying the paper _Dynamic Asynchronous Iterations_ by Matthew L. Daggitt and Timothy G Griffin submitted to Journal of Parallel and Distributed Computing in 2020. The latest version of the library can be found on the [master](https://github.com/MatthewDaggitt/agda-routing) branch in this repository.

## Proofs

All the definitions and proofs of the paper are found in the DIR=`RoutingLib.Iteration.Asynchronous.Dynamic` directory. (note that the equivalent definitions and proofs for the static asynchronous iterations can be found by replacing `Dynamic` with `Static` in the module name).

* Definition of a schedule is found in:
  [RoutingLib.Iteration.Asynchronous.Dynamic.Schedule](https://github.com/MatthewDaggitt/agda-routing/blob/jpdc2020/RoutingLib/Iteration/Asynchronous/Dynamic/Schedule.agda)

* Definition of a pseudoperiod is found in:
  [RoutingLib.Iteration.Asynchronous.Dynamic.Schedule.Pseudoperiod](https://github.com/MatthewDaggitt/agda-routing/blob/jpdc2020/RoutingLib/Iteration/Asynchronous/Dynamic/Schedule/Pseudoperiod.agda)

* Definition of the asynchronous iteration and correctness is in:
  [RoutingLib.Iteration.Asynchronous.Dynamic](https://github.com/MatthewDaggitt/agda-routing/blob/jpdc2020/RoutingLib/Iteration/Asynchronous/Dynamic.agda)

* Definitions of the various conditions sufficient for convergence are found in:
  [RoutingLib.Iteration.Asynchronous.Dynamic.Convergence.Conditions](https://github.com/MatthewDaggitt/agda-routing/blob/jpdc2020/RoutingLib/Iteration/Asynchronous/Dynamic/Convergence/Conditions.agda)

* Proof that our relaxed ACO conditions are equivalent to that of Uresin & Dubois:
  [RoutingLib.Iteration.Asynchronous.Dynamic.Convergence.RelaxACO](https://github.com/MatthewDaggitt/agda-routing/blob/jpdc2020/RoutingLib/Iteration/Asynchronous/Dynamic/Convergence/RelaxACO.agda)

* Proof of Theorem 1 that ACO implies convergence is found in:
  [RoutingLib.Iteration.Asynchronous.Dynamic.Convergence.ACOImpliesConverges](https://github.com/MatthewDaggitt/agda-routing/blob/jpdc2020/RoutingLib/Iteration/Asynchronous/Dynamic/Convergence/ACOImpliesConverges.agda)

* Counter-example to Proposition 3 and 4 of Uresin & Dubois is found in:
  [RoutingLib.Iteration.Asynchronous.Dynamic.Convergence.Counterexamples.UresinDubois3](https://github.com/MatthewDaggitt/agda-routing/blob/jpdc2020/RoutingLib/Iteration/Asynchronous/Dynamic/Convergence/Counterexamples/UresinDubois3.agda)

* Proof of Theorem 2 that our updated synchronous conditions implies ACO:
  [RoutingLib.Iteration.Asynchronous.Dynamic.Convergence.SyncImpliesACO](https://github.com/MatthewDaggitt/agda-routing/blob/jpdc2020/RoutingLib/Iteration/Asynchronous/Dynamic/Convergence/SyncImpliesACO.agda)

* Proof of Theorem 3 that AMCO implies ACO is found in:
  [RoutingLib.Iteration.Asynchronous.Dynamic.Convergence.AMCOImpliesACO](https://github.com/MatthewDaggitt/agda-routing/blob/jpdc2020/RoutingLib/Iteration/Asynchronous/Dynamic/Convergence/AMCOImpliesACO.agda)

* A public facing interface that users of the library should use to prove new convergence results is found at:
  [RoutingLib.Iteration.Asynchronous.Dynamic.Convergence](https://github.com/MatthewDaggitt/agda-routing/blob/jpdc2020/RoutingLib/Iteration/Asynchronous/Dynamic/Convergence.agda)

## Requirements

Requires Agda v2.6.1 and Standard Library v1.3

## Related work

[1] `Üresin, A`., `Dubois, M.` _Parallel asynchronous algorithms for discrete 
data_. J. ACM 37(3) (Jul 1990)

[2] `Gurney, A.J.T.` _Asynchronous iterations in ultrametric spaces_ (2017),
https://arxiv.org/abs/1701.07434

## Resulting publications

* `Daggitt, M.L.`, `Gurney, A.J.T`., `Griffin, T.G.`: _Asynchronous convergence
of policy-rich distributed bellman-ford routing protocols_ SIGCOMM (2018)

* `Daggitt, M.L`, `Griffin, T.G.` _Rate of convergence
of increasing path-vector routing protocols_ ICNP (2018)

* `Zmigrod, R.`, `Daggitt, M.L.`, `Griffin, T.G.` _An
Agda Formalization of Üresin & Dubois’ Asynchronous Fixed-Point
Theory_ ITP (2018).

* `Daggitt M.L.`, `Zmigrod, R.`, Griffin T.G.` _A Relaxation of Üresin & Dubois' 
Asynchronous Fixed-Point Theory in Agda_ JAR (2019)
