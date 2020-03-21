# Agda-routing for JPDC 2020

This library reasons about iterative asynchronous processes and network routing problems. It is organised in the same manner as the Agda standard library and contains extensions of several of the Agda standard library modules. The core contributions of this library can be found in the `RoutingLib.Iteration` and `RoutingLib.Routing` directories.

This is the frozen version of the library accompanying the paper _Dynamic Asynchronous Iterations_ by Matthew L. Daggitt and Timothy G Griffin submitted to Journal of Parallel and Distributed Computing in 2020. The latest version of the library can be found on the [master](https://github.com/MatthewDaggitt/agda-routing) branch of this repository.

## Proofs

All the definitions and proofs for dynamic asynchronous iterations in the paper are found in the `RoutingLib.Iteration.Asynchronous.Dynamic` directory. The equivalent definitions and proofs for the static asynchronous iterations can be found by replacing `Dynamic` with `Static` in the module name.

* Definition of a schedule (Definition 9) is found in:
  [RoutingLib.Iteration.Asynchronous.Dynamic.Schedule](https://github.com/MatthewDaggitt/agda-routing/blob/jpdc2020/RoutingLib/Iteration/Asynchronous/Dynamic/Schedule.agda)

* Definition of the asynchronous iteration (Definition 10) is in:
  [RoutingLib.Iteration.Asynchronous.Dynamic](https://github.com/MatthewDaggitt/agda-routing/blob/jpdc2020/RoutingLib/Iteration/Asynchronous/Dynamic.agda)

* Definitions for activation periods (Definition 11), expiry periods (Definition 12) and pseudocycles (Definition 13) are found in:
  [RoutingLib.Iteration.Asynchronous.Dynamic.Schedule.Pseudocycle](https://github.com/MatthewDaggitt/agda-routing/blob/jpdc2020/RoutingLib/Iteration/Asynchronous/Dynamic/Schedule/Pseudocycle.agda)

* Definitions of correctness (Definition 14) and accordant (Definition 15) are in:
  [RoutingLib.Iteration.Asynchronous.Dynamic](https://github.com/MatthewDaggitt/agda-routing/blob/jpdc2020/RoutingLib/Iteration/Asynchronous/Dynamic.agda)

* Definition of a dynamic ACO (Definition 16) is found in:
  [RoutingLib.Iteration.Asynchronous.Dynamic.Convergence.Conditions](https://github.com/MatthewDaggitt/agda-routing/blob/jpdc2020/RoutingLib/Iteration/Asynchronous/Dynamic/Convergence/Conditions.agda)

* The proof that any iteration that satisfies the dynamic ACO conditions is convergent (Theorem 3, Lemmas 1-8, Definitions 17-21) is found in:
  [RoutingLib.Iteration.Asynchronous.Dynamic.Convergence.ACOImpliesConvergent](https://github.com/MatthewDaggitt/agda-routing/blob/jpdc2020/RoutingLib/Iteration/Asynchronous/Dynamic/Convergence/ACOImpliesConvergent.agda)

* Definition of a dynamic AMCO (Definition 22) is found in:
  [RoutingLib.Iteration.Asynchronous.Dynamic.Convergence.Conditions](https://github.com/MatthewDaggitt/agda-routing/blob/jpdc2020/RoutingLib/Iteration/Asynchronous/Dynamic/Convergence/Conditions.agda)

* The proof that any iteration that satisfies the dynamic ACMO conditions also satisfies the dynamic ACO conditions (Theorem 4) is in: 
  [RoutingLib.Iteration.Asynchronous.Dynamic.Convergence.AMCOImpliesACO](https://github.com/MatthewDaggitt/agda-routing/blob/jpdc2020/RoutingLib/Iteration/Asynchronous/Dynamic/Convergence/AMCOImpliesACO.agda)

* A public facing interface re-exporting all the conditions and results is found in:
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
