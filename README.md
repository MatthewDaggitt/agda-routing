# Agda-routing

Requirements: Agda 2.6.2 and Standard Library 1.7

This library reasons about asynchronous iterative algorithms and network routing
problems. It is organised in the same manner as the Agda standard library and
contains extensions of several of the Agda standard library modules. The core
contributions of this library can be found in the `RoutingLib.Iteration` and
`RoutingLib.Routing` directories.

This is the frozen version of the library accompanying the paper 
`Formally Verified Convergence of Policy-Rich DBF Routing Protocols` 
by Matthew L. Daggitt and Timothy G Griffin. 
The latest version of the library can be found on the 
[master](https://github.com/MatthewDaggitt/agda-routing) branch in this repository.

Below is a guide that helps users match up the contents of the paper with the associated
formalisation in Agda.


## Section 2 - Model

### B. Paths

* Paths - [RoutingLib.Routing.Basics.Path.UncertifiedI](https://github.com/MatthewDaggitt/agda-routing/blob/ton2021/RoutingLib/Routing/Basics/Path/UncertifiedI.agda#L40)

### C. Routing algebras

* Definition 1: Routing algebra
  * The raw algebraic structure is in [RoutingLib.Routing.Algebra.Core](https://github.com/MatthewDaggitt/agda-routing/blob/ton2021/RoutingLib/Routing/Algebra/Core.agda#L36)
  * The axioms are in [RoutingLib.Routing.Algebra](https://github.com/MatthewDaggitt/agda-routing/blob/ton2021/RoutingLib/Routing/Algebra.agda#L100)

* Definition 2: Path algebra - [RoutingLib.Routing.Algebra](https://github.com/MatthewDaggitt/agda-routing/blob/ton2021/RoutingLib/Routing/Algebra.agda#L129)

* Some examples of basic routing algebras can be found in:
  * [RoutingLib.Routing.Protocols.ShortestPaths](https://github.com/MatthewDaggitt/agda-routing/blob/ton2021/RoutingLib/Routing/Protocols/ShortestPaths.agda#L23)
  * [RoutingLib.Routing.Protocols.WidestPaths](https://github.com/MatthewDaggitt/agda-routing/blob/ton2021/RoutingLib/Routing/Protocols/WidestPaths.agda#L23)
  * [RoutingLib.Routing.Protocols.ShortestWidestPaths](https://github.com/MatthewDaggitt/agda-routing/blob/ton2021/RoutingLib/Routing/Protocols/ShortestWidestPaths.agda#L25)

### D. Synchronous DBF protocol

* Adjacency matrices - [RoutingLib.Routing.Basics.Network](https://github.com/MatthewDaggitt/agda-routing/blob/ton2021/RoutingLib/Routing/Basics/Network.agda#L36)

* Routing tables/states - [RoutingLib.Routing.Basics.State](https://github.com/MatthewDaggitt/agda-routing/blob/ton2021/RoutingLib/Routing/Basics/State.agda#L48)

* Synchronous iteration - [RoutingLib.Routing.VectorBased.Synchronous](https://github.com/MatthewDaggitt/agda-routing/blob/ton2021/RoutingLib/Routing/VectorBased/Synchronous.agda#L35)

* Definition 3: Synchronous state function - [RoutingLib.Routing.VectorBased.Synchronous](https://github.com/MatthewDaggitt/agda-routing/blob/ton2021/RoutingLib/Routing/VectorBased/Synchronous.agda#L38)

### E. Asynchronous DBF protocol

* Definition 4: Schedules - [RoutingLib.Iteration.Asynchronous.Dynamic.Schedule](https://github.com/MatthewDaggitt/agda-routing/blob/ton2021/RoutingLib/Iteration/Asynchronous/Dynamic/Schedule.agda#L63)

* Definition 5: Participation topology - [RoutingLib.Routing.Basics.Network.Participants](https://github.com/MatthewDaggitt/agda-routing/blob/ton2021/RoutingLib/Routing/Basics/Network/Participants.agda#L41)

* Definition 6: Asynchronous state function - [RoutingLib.Iteration.Asynchronous.Dynamic](https://github.com/MatthewDaggitt/agda-routing/blob/ton2021/RoutingLib/Iteration/Asynchronous/Dynamic.agda#L138)

## Section 3 - Convergence results

### A. Some useful concepts

* Definition 7: Preference order over paths - [RoutingLib.Routing.Algebra.Core](https://github.com/MatthewDaggitt/agda-routing/blob/ton2021/RoutingLib/Routing/Algebra/Core.agda#L88)

* Definition 8: Assignments - [RoutingLib.Routing.Basics.Assignment](https://github.com/MatthewDaggitt/agda-routing/blob/ton2021/RoutingLib/Routing/Basics/Assignment.agda#L41)

* Definition 9: Preference order over assignments - [RoutingLib.Routing.Basics.Assignment](https://github.com/MatthewDaggitt/agda-routing/blob/ton2021/RoutingLib/Routing/Basics/Assignment.agda#L91)

* Definition 10: Extension relation - [RoutingLib.Routing.Basics.Assignment](https://github.com/MatthewDaggitt/agda-routing/blob/ton2021/RoutingLib/Routing/Basics/Assignment.agda#L125)

* Definition 11: Threatens relation - [RoutingLib.Routing.Basics.Assignment](https://github.com/MatthewDaggitt/agda-routing/blob/ton2021/RoutingLib/Routing/Basics/Assignment.agda#L136)

* Definition 12: Accordant states - [RoutingLib.Iteration.Asynchronous.Dynamic](https://github.com/MatthewDaggitt/agda-routing/blob/ton2021/RoutingLib/Iteration/Asynchronous/Dynamic.agda#L82)

### B. Convergence

* Pseudocycles - [RoutingLib.Iteration.Asynchronous.Dynamic.Schedule.Pseudoperiod](https://github.com/MatthewDaggitt/agda-routing/blob/ton2021/RoutingLib/Iteration/Asynchronous/Dynamic/Schedule/Pseudocycle.agda#L113)

* Definition 13: Convergent - [RoutingLib.Iteration.Asynchronous.Dynamic](https://github.com/MatthewDaggitt/agda-routing/blob/ton2021/RoutingLib/Iteration/Asynchronous/Dynamic.agda#L172)

### C. An existing convergence theorem

* Definition 14: AMCO - [RoutingLib.Iteration.Asynchronous.Dynamic.Convergence.Conditions](https://github.com/MatthewDaggitt/agda-routing/blob/ton2021/RoutingLib/Iteration/Asynchronous/Dynamic/Convergence/Conditions.agda#L105)

* Theorem 1: AMCO implies convergent - [RoutingLib.Iteration.Asynchronous.Dynamic.Convergence](https://github.com/MatthewDaggitt/agda-routing/blob/ton2021/RoutingLib/Iteration/Asynchronous/Dynamic/Convergence.agda#L114)

### D. Types of routing algebras

* Definition 15: Distributive routing algebra - [RoutingLib.Routing.Algebra](https://github.com/MatthewDaggitt/agda-routing/blob/ton2021/RoutingLib/Routing/Algebra.agda#L57)

* Definition 16: Increasing routing algebra - [RoutingLib.Routing.Algebra](https://github.com/MatthewDaggitt/agda-routing/blob/ton2021/RoutingLib/Routing/Algebra.agda#L60)

* Definition 17: Strictly increasing routing algebra - [RoutingLib.Routing.Algebra](https://github.com/MatthewDaggitt/agda-routing/blob/ton2021/RoutingLib/Routing/Algebra.agda#L64)

* Definition 18: Free network topology - [RoutingLib.Routing.Basics.Networks.Cycles](https://github.com/MatthewDaggitt/agda-routing/blob/ton2021/RoutingLib/Routing/Basics/Network/Cycles.agda#L69)

* Lemma 1: Strictly increasing implies network topology always free - [RoutingLib.Routing.Basics.Networks.Cycles](https://github.com/MatthewDaggitt/agda-routing/blob/ton2021/RoutingLib/Routing/Basics/Network/Cycles.agda#L211)

* Lemma 2: Increasing path algebras are always strictly increasing - [RoutingLib.Routing.Algebra.Properties.PathAlgebra](https://github.com/MatthewDaggitt/agda-routing/blob/ton2021/RoutingLib/Routing/Algebra/Properties/PathAlgebra.agda#L42)

### E. DBF convergence results

* Theorem 2: Finite DV protocols convergent over free network topologies - [RoutingLib.Routing.VectorBased.Convergence.Results](https://github.com/MatthewDaggitt/agda-routing/blob/ton2021/RoutingLib/Routing/VectorBased/Convergence/Results.agda#L56)

* Theorem 3: Strictly increasing, finite DV protocols always convergent - [RoutingLib.Routing.VectorBased.Convergence.Results](https://github.com/MatthewDaggitt/agda-routing/blob/ton2021/RoutingLib/Routing/VectorBased/Convergence/Results.agda#L65)

* Theorem 4: PV protocols convergent over free network topologies - [RoutingLib.Routing.VectorBased.Convergence.Results](https://github.com/MatthewDaggitt/agda-routing/blob/ton2021/RoutingLib/Routing/VectorBased/Convergence/Results.agda#L79)

* Theorem 5: Strictly increasing PV protocols always convergent - [RoutingLib.Routing.VectorBased.Convergence.Results](https://github.com/MatthewDaggitt/agda-routing/blob/ton2021/RoutingLib/Routing/VectorBased/Convergence/Results.agda#L87)

## Section 5: A safe-by-design algebra

* Local preferences - [RoutingLib.Routing.Protocols.BGPLite.LocalPref](https://github.com/MatthewDaggitt/agda-routing/blob/ton2021/RoutingLib/Routing/Protocols/BGPLite/LocalPref.agda#L18)

* Communities - [RoutingLib.Routing.Protocols.BGPLite.Communities](https://github.com/MatthewDaggitt/agda-routing/blob/ton2021/RoutingLib/Routing/Protocols/BGPLite/Communities.agda#L37)

* Path weights - [RoutingLib.Routing.Protocols.BGPLite.PathWeights](https://github.com/MatthewDaggitt/agda-routing/blob/ton2021/RoutingLib/Routing/Protocols/BGPLite/PathWeights.agda#L34)

* Trivial route - [RoutingLib.Routing.Protocols.BGPLite.Core](https://github.com/MatthewDaggitt/agda-routing/blob/ton2021/RoutingLib/Routing/Protocols/BGPLite/Core.agda#L45)

* Invalid route - [RoutingLib.Routing.Protocols.BGPLite.Core](https://github.com/MatthewDaggitt/agda-routing/blob/ton2021/RoutingLib/Routing/Protocols/BGPLite/Core.agda#L48)

* Choice - [RoutingLib.Routing.Protocols.BGPLite.Core](https://github.com/MatthewDaggitt/agda-routing/blob/ton2021/RoutingLib/Routing/Protocols/BGPLite/Core.agda#L52)

* Condition language - [RoutingLib.Routing.Protocols.BGPLite.Policies](https://github.com/MatthewDaggitt/agda-routing/blob/ton2021/RoutingLib/Routing/Protocols/BGPLite/Policies.agda#L35)

* Condition evaluation - [RoutingLib.Routing.Protocols.BGPLite.Policies](https://github.com/MatthewDaggitt/agda-routing/blob/ton2021/RoutingLib/Routing/Protocols/BGPLite/Policies.agda#L43)

* Policy language - [RoutingLib.Routing.Protocols.BGPLite.Policies](https://github.com/MatthewDaggitt/agda-routing/blob/ton2021/RoutingLib/Routing/Protocols/BGPLite/Policies.agda#L57)

* Policy evaluation - [RoutingLib.Routing.Protocols.BGPLite.Policies](https://github.com/MatthewDaggitt/agda-routing/blob/ton2021/RoutingLib/Routing/Protocols/BGPLite/Policies.agda#L67)

* Extension - [RoutingLib.Routing.Protocols.BGPLite.Core](https://github.com/MatthewDaggitt/agda-routing/blob/ton2021/RoutingLib/Routing/Protocols/BGPLite/Core.agda#L42)

* Extension application - [RoutingLib.Routing.Protocols.BGPLite.Core](https://github.com/MatthewDaggitt/agda-routing/blob/ton2021/RoutingLib/Routing/Protocols/BGPLite/Core.agda#L66)

* Path function - [RoutingLib.Routing.Protocols.BGPLite.Simulation](https://github.com/MatthewDaggitt/agda-routing/blob/ton2021/RoutingLib/Routing/Protocols/BGPLite/Simulation.agda#L127)

* Algebra - [RoutingLib.Routing.Protocols.BGPLite.Core](https://github.com/MatthewDaggitt/agda-routing/blob/ton2021/RoutingLib/Routing/Protocols/BGPLite/Core.agda#L89)

* Proof of convergence - [RoutingLib.Routing.Protocols.BGPLite.Core](https://github.com/MatthewDaggitt/agda-routing/blob/ton2021/RoutingLib/Routing/Protocols/BGPLite.agda#L32)


## Appendix B - Distance-vector proof

* Dislogment order
 * Definition - [RoutingLib.Routing.VectorBased.Asynchronous.Convergence.Step1_FreeImpliesERO](https://github.com/MatthewDaggitt/agda-routing/blob/ton2021/RoutingLib/Routing/VectorBased/Asynchronous/Convergence/Step1_FreeImpliesERO.agda#L90)
 * Properties - [RoutingLib.Routing.VectorBased.Asynchronous.Convergence.Step1_FreeImpliesERO](https://github.com/MatthewDaggitt/agda-routing/blob/ton2021/RoutingLib/Routing/VectorBased/Asynchronous/Convergence/Step1_FreeImpliesERO.agda#L224)

* Height function
  * Definition - [RoutingLib.Routing.VectorBased.Asynchronous.Convergence.Step2_EROImpliesHF](https://github.com/MatthewDaggitt/agda-routing/blob/ton2021/RoutingLib/Routing/VectorBased/Asynchronous/Convergence/Step2_EROImpliesHF.agda#L91)
 * Properties - [RoutingLib.Routing.VectorBased.Asynchronous.Convergence.Step2_EROImpliesHF](https://github.com/MatthewDaggitt/agda-routing/blob/ton2021/RoutingLib/Routing/VectorBased/Asynchronous/Convergence/Step2_EROImpliesHF.agda#L116)

* Distance function over path-weights
  * Definition - [RoutingLib.Routing.VectorBased.Asynchronous.Convergence.Step3_HFImpliesDF_DistanceVector](https://github.com/MatthewDaggitt/agda-routing/blob/ton2021/RoutingLib/Routing/VectorBased/Asynchronous/Convergence/Step3_HFImpliesDF_DistanceVector.agda#L63)
  * Properties - [RoutingLib.Routing.VectorBased.Asynchronous.Convergence.Step3_HFImpliesDF_DistanceVector](https://github.com/MatthewDaggitt/agda-routing/blob/ton2021/RoutingLib/Routing/VectorBased/Asynchronous/Convergence/Step3_HFImpliesDF_DistanceVector.agda#L200)

* Distance function over routing tables - [RoutingLib.Routing.VectorBased.Asynchronous.Convergence.Step4_DFImpliesAMCO](https://github.com/MatthewDaggitt/agda-routing/blob/ton2021/RoutingLib/Routing/VectorBased/Asynchronous/Convergence/Step4_DFImpliesAMCO.agda#L60)

* Distance function over routing states - [RoutingLib.Routing.VectorBased.Asynchronous.Convergence.Step4_DFImpliesAMCO](https://github.com/MatthewDaggitt/agda-routing/blob/ton2021/RoutingLib/Routing/VectorBased/Asynchronous/Convergence/Step4_DFImpliesAMCO.agda#L68)

* Lemma 3: Routers always use the trivial route to themselves - [RoutingLib.Routing.VectorBased.Synchronous.DistanceVector.Properties](https://github.com/MatthewDaggitt/agda-routing/blob/ton2021/RoutingLib/Routing/VectorBased/Synchronous/DistanceVector/Properties.agda#L63)

* Lemma 4: Distance strictly decreases after an iteration - [RoutingLib.Routing.VectorBased.Asynchronous.Convergence.Step3_HFImpliesDF_DistanceVector](https://github.com/MatthewDaggitt/agda-routing/blob/ton2021/RoutingLib/Routing/VectorBased/Asynchronous/Convergence/Step3_HFImpliesDF_DistanceVector.agda#L173)

* Lemma 5: Synchronous iteration is strictly contracting
 - Strictly contracting on orbits - [RoutingLib.Routing.VectorBased.Asynchronous.Convergence.Step4_DFImpliesAMCO](https://github.com/MatthewDaggitt/agda-routing/blob/ton2021/RoutingLib/Routing/VectorBased/Asynchronous/Convergence/Step4_DFImpliesAMCO.agda#L153)
 - Strictly contracting on fixed points - [RoutingLib.Routing.VectorBased.Asynchronous.Convergence.Step4_DFImpliesAMCO](https://github.com/MatthewDaggitt/agda-routing/blob/ton2021/RoutingLib/Routing/VectorBased/Asynchronous/Convergence/Step4_DFImpliesAMCO.agda#L157)

* The synchronous iteration is an AMCO - [RoutingLib.Routing.VectorBased.Asynchronous.Convergence.Step4_DFImpliesAMCO](https://github.com/MatthewDaggitt/agda-routing/blob/ton2021/RoutingLib/Routing/VectorBased/Asynchronous/Convergence/Step4_DFImpliesAMCO.agda#L161)

## Appendix C - Path-vector proof

* Definition 19: Weight of a path - [RoutingLib.Routing.Algebra](https://github.com/MatthewDaggitt/agda-routing/blob/ton2021/RoutingLib/Routing/Algebra.agda#L190)

* Definition 20: Consistent path weights - [RoutingLib.Routing.Algebra.Construct.Consistent](https://github.com/MatthewDaggitt/agda-routing/blob/ton2021/RoutingLib/Routing/Algebra/Construct/Consistent.agda#L75)

* Lemma 6: Choice preserves consistency - [RoutingLib.Routing.Algebra.Construct.Consistent](https://github.com/MatthewDaggitt/agda-routing/blob/ton2021/RoutingLib/Routing/Algebra/Construct/Consistent.agda#L102)

* Lemma 7: Extension preserves consistency - [RoutingLib.Routing.Algebra.Construct.Consistent](https://github.com/MatthewDaggitt/agda-routing/blob/ton2021/RoutingLib/Routing/Algebra/Construct/Consistent.agda#L107)

* Lemma 8: Synchronous iteration preserves consistency - [RoutingLib.Routing.VectorBased.Synchronous.PathVector.Properties](https://github.com/MatthewDaggitt/agda-routing/blob/ton2021/RoutingLib/Routing/VectorBased/Synchronous/PathVector/Properties.agda#L157)

* Lemma 9: The set of consistent path weights is finite - [RoutingLib.Routing.Algebra.Construct.Consistent](https://github.com/MatthewDaggitt/agda-routing/blob/ton2021/RoutingLib/Routing/Algebra/Construct/Consistent.agda#L343)

* Inconsistent height of path-weights: [RoutingLib.Routing.VectorBased.Asynchronous.Convergence.Step3_HFImpliesDF_PathVector](https://github.com/MatthewDaggitt/agda-routing/blob/ton2021/RoutingLib/Routing/VectorBased/Asynchronous/Convergence/Step3_HFImpliesDF_PathVector.agda#L56)

* Distance function over inconsistent path-weights: [RoutingLib.Routing.VectorBased.Asynchronous.Convergence.Step3_HFImpliesDF_PathVector](https://github.com/MatthewDaggitt/agda-routing/blob/ton2021/RoutingLib/Routing/VectorBased/Asynchronous/Convergence/Step3_HFImpliesDF_PathVector.agda#L62)

* Distance function over consistent path-weights: [RoutingLib.Routing.VectorBased.Asynchronous.Convergence.Step3_HFImpliesDF_PathVector](https://github.com/MatthewDaggitt/agda-routing/blob/ton2021/RoutingLib/Routing/VectorBased/Asynchronous/Convergence/Step3_HFImpliesDF_PathVector.agda#L67)

* Distance function over path-weights: [RoutingLib.Routing.VectorBased.Asynchronous.Convergence.Step3_HFImpliesDF_PathVector](https://github.com/MatthewDaggitt/agda-routing/blob/ton2021/RoutingLib/Routing/VectorBased/Asynchronous/Convergence/Step3_HFImpliesDF_PathVector.agda#L70)

* Distance function over routing tables - [RoutingLib.Routing.VectorBased.Asynchronous.Convergence.Step4_DFImpliesAMCO](https://github.com/MatthewDaggitt/agda-routing/blob/ton2021/RoutingLib/Routing/VectorBased/Asynchronous/Convergence/Step4_DFImpliesAMCO.agda#L60)

* Distance function over routing states - [RoutingLib.Routing.VectorBased.Asynchronous.Convergence.Step4_DFImpliesAMCO](https://github.com/MatthewDaggitt/agda-routing/blob/ton2021/RoutingLib/Routing/VectorBased/Asynchronous/Convergence/Step4_DFImpliesAMCO.agda#L68)

* Lemma 11: Inconsistent routes cannot remain constant - [RoutingLib.Routing.VectorBased.Synchronous.PathVector.Properties](https://github.com/MatthewDaggitt/agda-routing/blob/ton2021/RoutingLib/Routing/VectorBased/Synchronous/PathVector/Properties.agda#L167)

* Lemma 12: Distance strictly decreases after consecutative iteration - [RoutingLib.Routing.VectorBased.Asynchronous.Convergence.Step3_HFImpliesDF_PathVector](https://github.com/MatthewDaggitt/agda-routing/blob/ton2021/RoutingLib/Routing/VectorBased/Asynchronous/Convergence/Step3_HFImpliesDF_PathVector.agda#L465)

* Lemma 13: Synchronous iteration is strictly contracting on orbits - [RoutingLib.Routing.VectorBased.Asynchronous.Convergence.Step4_DFImpliesAMCO](https://github.com/MatthewDaggitt/agda-routing/blob/ton2021/RoutingLib/Routing/VectorBased/Asynchronous/Convergence/Step4_DFImpliesAMCO.agda#L153)

* Lemma 14: Synchronous iteration is strictly contracting on fixed points - [RoutingLib.Routing.VectorBased.Asynchronous.Convergence.Step4_DFImpliesAMCO](https://github.com/MatthewDaggitt/agda-routing/blob/ton2021/RoutingLib/Routing/VectorBased/Asynchronous/Convergence/Step4_DFImpliesAMCO.agda#L157)

* The synchronous iteration is an AMCO - [RoutingLib.Routing.VectorBased.Asynchronous.Convergence.Step4_DFImpliesAMCO](https://github.com/MatthewDaggitt/agda-routing/blob/ton2021/RoutingLib/Routing/VectorBased/Asynchronous/Convergence/Step4_DFImpliesAMCO.agda#L161)
