# Agda-routing for JPDC 2020

This library reasons about iterative asynchronous processes and network routing problems. It is organised in the same manner as the Agda standard library and contains extensions of several of the Agda standard library modules. The core contributions of this library can be found in the `RoutingLib.Iteration` and `RoutingLib.Routing` directories.

This is the frozen version of the library accompanying the paper _Dynamic Asynchronous Iterations_ by Matthew L. Daggitt and Timothy G Griffin submitted to Journal of Parallel and Distributed Computing in 2020. The latest version of the library can be found on the [master](https://github.com/MatthewDaggitt/agda-routing) branch of this repository.

## Proofs

All the definitions and proofs for dynamic asynchronous iterations in the paper are found in the `RoutingLib.Iteration.Asynchronous.Dynamic` directory. The equivalent definitions and proofs for the static asynchronous iterations can be found by replacing `Dynamic` with `Static` in the module name.

* Definition 9 for a schedule is found in:
  [RoutingLib.Iteration.Asynchronous.Dynamic.Schedule](https://github.com/MatthewDaggitt/agda-routing/blob/jpdc2020/RoutingLib/Iteration/Asynchronous/Dynamic/Schedule.agda)

* Definition 10 for the asynchronous state function is in:
  [RoutingLib.Iteration.Asynchronous.Dynamic](https://github.com/MatthewDaggitt/agda-routing/blob/jpdc2020/RoutingLib/Iteration/Asynchronous/Dynamic.agda)

* Definitions 11, 12 & 13 for activation periods, expiry periods and pseudocycles are in:
  [RoutingLib.Iteration.Asynchronous.Dynamic.Schedule.Pseudocycle](https://github.com/MatthewDaggitt/agda-routing/blob/jpdc2020/RoutingLib/Iteration/Asynchronous/Dynamic/Schedule/Pseudocycle.agda)

* Definitions 14 & 15 of correctness and accordant are in:
  [RoutingLib.Iteration.Asynchronous.Dynamic](https://github.com/MatthewDaggitt/agda-routing/blob/jpdc2020/RoutingLib/Iteration/Asynchronous/Dynamic.agda)

* Definition 16 for the dynamic ACO conditions is found in:
  [RoutingLib.Iteration.Asynchronous.Dynamic.Convergence.Conditions](https://github.com/MatthewDaggitt/agda-routing/blob/jpdc2020/RoutingLib/Iteration/Asynchronous/Dynamic/Convergence/Conditions.agda)

* Theorem 3 (including Lemmas 1-8 and Definitions 17-21) that any iteration that satisfies the dynamic ACO conditions is convergent is found in:
  [RoutingLib.Iteration.Asynchronous.Dynamic.Convergence.ACOImpliesConvergent](https://github.com/MatthewDaggitt/agda-routing/blob/jpdc2020/RoutingLib/Iteration/Asynchronous/Dynamic/Convergence/ACOImpliesConvergent.agda)

* Definition 22 for the dynamic AMCO conditions is found in:
  [RoutingLib.Iteration.Asynchronous.Dynamic.Convergence.Conditions](https://github.com/MatthewDaggitt/agda-routing/blob/jpdc2020/RoutingLib/Iteration/Asynchronous/Dynamic/Convergence/Conditions.agda)

* Theorem 4 that any iteration that satisfies the dynamic ACMO conditions also satisfies the dynamic ACO conditions is in: 
  [RoutingLib.Iteration.Asynchronous.Dynamic.Convergence.AMCOImpliesACO](https://github.com/MatthewDaggitt/agda-routing/blob/jpdc2020/RoutingLib/Iteration/Asynchronous/Dynamic/Convergence/AMCOImpliesACO.agda)

* A public facing interface re-exporting all the conditions and results is found in:
  [RoutingLib.Iteration.Asynchronous.Dynamic.Convergence](https://github.com/MatthewDaggitt/agda-routing/blob/jpdc2020/RoutingLib/Iteration/Asynchronous/Dynamic/Convergence.agda)

## Requirements

Requires Agda v2.6.1 and Standard Library v1.3.

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
