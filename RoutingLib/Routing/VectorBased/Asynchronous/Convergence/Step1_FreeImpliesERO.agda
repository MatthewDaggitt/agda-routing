open import Data.Nat as ℕ using (ℕ; zero; suc; _≤_; z≤n; s≤s)
open import Data.Fin using (Fin; suc; inject₁)
open import Data.Fin.Patterns
open import Data.List hiding ([_]; last)
open import Data.Sum as Sum using (_⊎_; inj₁; inj₂)
open import Data.Product as Product using (∃; ∃₂; _,_; proj₁; proj₂; _×_)
open import Data.Maybe
open import Data.Maybe.Relation.Unary.Any
open import Data.Maybe.Relation.Unary.All as All
open import Data.Unit using (tt)
open import Function
open import Induction.WellFounded using (WellFounded; Acc; acc)
open import Level using (Level; _⊔_) renaming (suc to lsuc)
open import Relation.Binary hiding (NonEmpty)
open import Relation.Binary.Construct.Union as Union using (_∪_)
open import Relation.Binary.Construct.Closure.Transitive as TransClosure
  hiding ([_]; _∷_)
import Relation.Binary.Construct.NonStrictToStrict as NonStrictToStrict
open import Relation.Binary.PropositionalEquality
import Relation.Binary.Construct.Union as Union
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Nullary.Decidable using (False; fromWitnessFalse)

open import RoutingLib.Data.Sum
open import RoutingLib.Data.Fin using (_+ₘ_; _-ₘ_)
open import RoutingLib.Data.FiniteSet renaming (FiniteSet to FiniteSet⁺)
open import RoutingLib.Relation.Nullary.Finite.Bijection.Setoid using (Finite)
open import RoutingLib.Data.Maybe.Properties
open import RoutingLib.Relation.Binary using (StrictMinimum)
import RoutingLib.Relation.Binary.Construct.Closure.Transitive.Finite as TransClosure
import RoutingLib.Relation.Binary.Construct.Closure.Transitive as TransClosure
open import RoutingLib.Relation.Binary.Construct.Closure.Transitive.Any

open import RoutingLib.Routing using (AdjacencyMatrix)
open import RoutingLib.Routing.Algebra

module RoutingLib.Routing.VectorBased.Asynchronous.Convergence.Step1_FreeImpliesERO
  {a b ℓ} {algebra : RawRoutingAlgebra a b ℓ}
  (isRoutingAlgebra : IsRoutingAlgebra algebra)
  {n} (A : AdjacencyMatrix algebra n)
  where

open RawRoutingAlgebra algebra
open IsRoutingAlgebra isRoutingAlgebra

open import RoutingLib.Routing algebra n
open import RoutingLib.Routing.AdjacencyMatrix.Cycles algebra
open import RoutingLib.Routing.AdjacencyMatrix.Relations algebra A
open import RoutingLib.Routing.AdjacencyMatrix.Relations.Properties isRoutingAlgebra A
open import RoutingLib.Routing.Algebra.Properties.RoutingAlgebra isRoutingAlgebra

open import Data.List.Membership.Setoid S
open import Data.List.Relation.Binary.Sublist.Setoid S
open import Data.List.Relation.Binary.Sublist.Setoid.Properties S
open import RoutingLib.Data.List.Relation.Binary.Sublist.Setoid S
open import RoutingLib.Data.List.Relation.Binary.Sublist.Setoid.Properties S



open import RoutingLib.Routing.VectorBased.Asynchronous.Convergence.Definitions algebra

open import Relation.Binary.Reasoning.PartialOrder ≤₊-poset

private
  variable
    x y : Route
    
--------------------------------------------------------------------------------
-- An ordering over routes
--------------------------------------------------------------------------------
-- In order to build a height function all we need to have is a
-- strict partial order over routes with the property `x < Aᵢⱼ(x)`. When
-- the algebra is strictly increasing this is simply `_<₊_`. However when the
-- network is cycle free we must come up with something more complicated. The
-- hard part is proving that any such order is irreflexive, i.e. it has no
-- cycles in it.

-- The relation below is a generalisation of the dispute digraph. It says that
-- route `x` is less than route `y` if there exists some path of either
-- `<₊ = is preferred to` or `↝ = can be extended to` relations between them.
-- It is more general than the dispute digraph as used by both Griffin and
-- Sobrinho, as a) it doesn't require all the routes to have the same source
-- (something not easily expressible in an algebra) and b) it weakens
-- distributivity violation links to merely `can be extended to` links.

infix 4 _<ᶠ_

_<ᶠ_ : Rel Route (a ⊔ ℓ)
_<ᶠ_ = TransClosure (_<₊_ ∪ _↝_)

-- Predicates stating whether a path contains any extensions

↝∈_ : x <ᶠ y → Set
↝∈_ = AnyEdge IsInj₂

↝∉_ : x <ᶠ y → Set
↝∉ x = ¬ (↝∈ x)

-- It's decidable if a path contains any extensions

↝∈?_ : (x<ᶠy : x <ᶠ y) → Dec (↝∈ x<ᶠy)
↝∈?_ = anyEdge? isInj₂?

-- If the set of extended routes are empty then the first route in the
-- path must be strictly preferred to the last route in the path.
↝∉⇒x<₊y : (x<y : x <ᶠ y) → ↝∉ x<y → x <₊ y
↝∉⇒x<₊y [ inj₁ x<y ]     _  = x<y
↝∉⇒x<₊y [ inj₂ x<y ]     ↝∉ = contradiction (here₁ _) ↝∉
↝∉⇒x<₊y (inj₁ x<y ∷ y<z) ↝∉ = <₊-trans x<y (↝∉⇒x<₊y y<z (↝∉ ∘ there))
↝∉⇒x<₊y (inj₂ x↝y ∷ y<z) ↝∉ with ↝∈? y<z
... | no _  = contradiction (here₂ _) ↝∉
... | yes _ = contradiction (here₂ _) ↝∉

-- Given two related routes, i.e. path through this graph, we identify the set
-- of routes that are extended. If extensions exist in the path we return
-- nothing, otherwise we return a non-empty set of routes.
extendedRoutes : (x<ᶠy : x <ᶠ y) → ↝∈ x<ᶠy → FiniteSet⁺ Route
extendedRoutes {x} [ inj₁ x<y ]      (here₁ ())
extendedRoutes {x} [ inj₂ x↝y ]      _          = ⟦ x ⟧
extendedRoutes {x} (inj₁ x<z ∷ z<ᶠy) (there ↝∈) = extendedRoutes z<ᶠy ↝∈ 
extendedRoutes {x} (inj₂ x↝z ∷ z<ᶠy) _          with ↝∈? z<ᶠy
... | no  _   = ⟦ x ⟧
... | yes ext = ⟦ x ⟧∪ extendedRoutes z<ᶠy ext

-- If some route `v` is preferred to the start point of the path then `v` must also
-- be preferred to the first extended route in the path (if it exists).
v≤x⇒v≤er[x<ᶠy]₀ : ∀ {v} → v ≤₊ x → (x<ᶠy : x <ᶠ y) → (↝∈x<y : ↝∈ x<ᶠy) →
                 v ≤₊ first (extendedRoutes x<ᶠy ↝∈x<y)
v≤x⇒v≤er[x<ᶠy]₀ v≤x [ inj₁ _ ]        (here₁ ()) 
v≤x⇒v≤er[x<ᶠy]₀ v≤x [ inj₂ _ ]        _          = v≤x
v≤x⇒v≤er[x<ᶠy]₀ v≤x (inj₁ x<z ∷ z<ᶠy) (there ↝∈) = v≤x⇒v≤er[x<ᶠy]₀ (≤₊-trans v≤x (<₊⇒≤₊ x<z)) z<ᶠy ↝∈
v≤x⇒v≤er[x<ᶠy]₀ v≤x (inj₂ x↝z ∷ z<ᶠy) _          with ↝∈? z<ᶠy
... | no  _ = v≤x
... | yes _ = v≤x

-- If the end point of the path is preferred to some route `v` then last extended route
-- in the path (if it exists) must be dominated by `v`.
y≤v⇒er[x<ᶠy]₋₁⊴v : ∀ {v} → y ≤₊ v → (x<ᶠy : x <ᶠ y) → (↝∈x<y : ↝∈ x<ᶠy) →
                  last (extendedRoutes x<ᶠy ↝∈x<y) ⊴ v
y≤v⇒er[x<ᶠy]₋₁⊴v y≤v [ inj₁ x<y ]      (here₁ ()) 
y≤v⇒er[x<ᶠy]₋₁⊴v y≤v [ inj₂ x↝y ]      _          = ⊴-≤₊-trans (↝⇒⊴ x↝y) y≤v
y≤v⇒er[x<ᶠy]₋₁⊴v y≤v (inj₁ x<z ∷ z<ᶠy) (there ↝∈) = y≤v⇒er[x<ᶠy]₋₁⊴v y≤v z<ᶠy ↝∈
y≤v⇒er[x<ᶠy]₋₁⊴v y≤v (inj₂ x↝w ∷ w<ᶠy) _          with ↝∈? w<ᶠy
... | no  ↝∉w<ᶠy = ⊴-≤₊-trans (↝⇒⊴ x↝w) (≤₊-trans (proj₁ (↝∉⇒x<₊y w<ᶠy ↝∉w<ᶠy)) y≤v)
... | yes ↝∈w<ᶠy = y≤v⇒er[x<ᶠy]₋₁⊴v y≤v w<ᶠy ↝∈w<ᶠy

-- The iᵗʰ extended route in the path is threatened by i+1ᵗʰ extended route in the path
⟦y<ᶠz⟧↝ᵢ⊴⟦y<ᶠz⟧↝ᵢ₊₁ : (x<ᶠy : x <ᶠ y) → (↝∈x<y : ↝∈ x<ᶠy) →
                      let er = extendedRoutes x<ᶠy ↝∈x<y in
                      ∀ i → iᵗʰ er (inject₁ i) ⊴ iᵗʰ er (suc i)
⟦y<ᶠz⟧↝ᵢ⊴⟦y<ᶠz⟧↝ᵢ₊₁ [ inj₁ _ ]         (here₁ ())
⟦y<ᶠz⟧↝ᵢ⊴⟦y<ᶠz⟧↝ᵢ₊₁ [ inj₂ _ ]         _          = λ()
⟦y<ᶠz⟧↝ᵢ⊴⟦y<ᶠz⟧↝ᵢ₊₁ (inj₁ x≤z ∷ z<ᶠy)  (there ↝∈) = ⟦y<ᶠz⟧↝ᵢ⊴⟦y<ᶠz⟧↝ᵢ₊₁ z<ᶠy ↝∈
⟦y<ᶠz⟧↝ᵢ⊴⟦y<ᶠz⟧↝ᵢ₊₁ {x} {y} (_∷_ {y = z} (inj₂ x↝z) z<ᶠy) _ with ↝∈? z<ᶠy
... | no  ↝∉z<ᶠy = λ()
... | yes ↝∈z<ᶠy = λ
  { 0F      → ⊴-≤₊-trans (↝⇒⊴ x↝z) (v≤x⇒v≤er[x<ᶠy]₀ ≤₊-refl z<ᶠy ↝∈z<ᶠy)
  ; (suc i) → ⟦y<ᶠz⟧↝ᵢ⊴⟦y<ᶠz⟧↝ᵢ₊₁ z<ᶠy ↝∈z<ᶠy i
  }

-- When the topology is cycle free then irreflexivity can now be proved. This follows
-- as if the start point of the path is equal to the end point then:
--   ∙ if the path contains no extensions then x ≈ y and x <₊ y which is contradiction
--     by the irreflexivity of _<₊_
--   ∙ if the path does contain extensions then the set of extended routes must form
--     a cycle thanks to x ≈ y and the previous lemmas.
.<ᶠ-irrefl : CycleFree A → Irreflexive _≈_ _<ᶠ_
<ᶠ-irrefl cf x≈y x<ᶠy with ↝∈? x<ᶠy
... | no  ↝∉x<ᶠy = <₊-irrefl x≈y (↝∉⇒x<₊y x<ᶠy ↝∉x<ᶠy)
... | yes ↝∈x<ᶠy = cf (extendedRoutes x<ᶠy ↝∈x<ᶠy) er[x<ᶠy]-cyclic
  where
  ⟦x<ᶠy⟧₋₁⊴x         = y≤v⇒er[x<ᶠy]₋₁⊴v ≤₊-refl x<ᶠy ↝∈x<ᶠy
  x≤⟦x<ᶠy⟧₀          = v≤x⇒v≤er[x<ᶠy]₀ (≤₊-reflexive (≈-sym x≈y)) x<ᶠy ↝∈x<ᶠy
  ⟦x<ᶠy⟧ᵢ⊴⟦x<ᶠy⟧ᵢ₊₁  = ⟦y<ᶠz⟧↝ᵢ⊴⟦y<ᶠz⟧↝ᵢ₊₁ x<ᶠy ↝∈x<ᶠy
 
  er[x<ᶠy]-cyclic : Cyclic A (extendedRoutes x<ᶠy ↝∈x<ᶠy)
  er[x<ᶠy]-cyclic 0F      = ⊴-≤₊-trans ⟦x<ᶠy⟧₋₁⊴x x≤⟦x<ᶠy⟧₀
  er[x<ᶠy]-cyclic (suc i) = ⟦x<ᶠy⟧ᵢ⊴⟦x<ᶠy⟧ᵢ₊₁ i

<ᶠ-trans : Transitive _<ᶠ_
<ᶠ-trans = TransClosure.trans

<ᶠ-respʳ-≈ : _<ᶠ_ Respectsʳ _≈_
<ᶠ-respʳ-≈ = TransClosure.R⁺-respʳ-≈ (Union.respʳ _<₊_ _↝_ <₊-respʳ-≈ ↝-respʳ-≈)

<ᶠ-respˡ-≈ : _<ᶠ_ Respectsˡ _≈_
<ᶠ-respˡ-≈ = TransClosure.R⁺-respˡ-≈ (Union.respˡ _<₊_ _↝_ <₊-respˡ-≈ ↝-respˡ-≈)

<ᶠ-resp-≈ : _<ᶠ_ Respects₂ _≈_
<ᶠ-resp-≈ = <ᶠ-respʳ-≈ , <ᶠ-respˡ-≈

<ᶠ-dec : Finite S → Decidable _<ᶠ_
<ᶠ-dec fin = TransClosure.R⁺? {S = S} fin (Union.resp₂ <₊-resp-≈ ↝-resp-≈) (Union.decidable _<₊?_ _↝?_)

<ᶠ-min : StrictMinimum _≈_ _<ᶠ_ 0#
<ᶠ-min {x} x≉0 = [ inj₁ (≤₊-minimum x , x≉0 ∘ ≈-sym) ]

-- And importantly `x` is strictly less than `Aᵢⱼ(x)` even though the algebra
-- is not necessarily strictly increasing.
↝⇒<ᶠ : ∀ {x y} → x ↝ y → x <ᶠ y
↝⇒<ᶠ x↝y = [ inj₂ x↝y ]

<₊∧<ᶠ⇒<ᶠ : Trans _<₊_ _<ᶠ_ _<ᶠ_
<₊∧<ᶠ⇒<ᶠ x<₊y y<ᶠz = inj₁ x<₊y ∷ y<ᶠz

<ᶠ-extensionRespectingOrder : IsFinite algebra → .(CycleFree A) → ExtensionRespectingOrder A _
<ᶠ-extensionRespectingOrder fin cf = record
  { _<ᵣ_       = _<ᶠ_
  ; ↝⇒<ᵣ       = ↝⇒<ᶠ
  ; <₊∧<ᵣ⇒<ᵣ   = <₊∧<ᶠ⇒<ᶠ
  ; <ᵣ-irrefl  = <ᶠ-irrefl cf
  ; <ᵣ-trans   = <ᶠ-trans
  ; _<ᵣ?_      = <ᶠ-dec fin
  ; <ᵣ-respʳ-≈ = <ᶠ-respʳ-≈
  ; <ᵣ-respˡ-≈ = <ᶠ-respˡ-≈
  ; <ᵣ-min     = <ᶠ-min
  }
