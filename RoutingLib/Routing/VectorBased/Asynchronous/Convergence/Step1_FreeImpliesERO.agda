open import Data.Nat as ℕ using (ℕ; zero; suc; pred; _≤_; z≤n; s≤s)
open import Data.Fin using (Fin; suc; inject₁)
open import Data.Fin.Patterns
open import Data.List hiding ([_]; last)
open import Data.Sum as Sum using (_⊎_; inj₁; inj₂)
open import Data.Product as Product using (Σ; ∃; ∃₂; _,_; proj₁; proj₂; _×_)
open import Data.Maybe
open import Data.Maybe.Relation.Unary.Any
open import Data.Maybe.Relation.Unary.All as All
open import Data.Unit using (tt)
open import Data.Vec.Functional using (Vector)
open import Function
open import Induction.WellFounded using (WellFounded; Acc; acc)
open import Level using (Level; _⊔_) renaming (suc to lsuc)
open import Relation.Binary hiding (NonEmpty)
open import Relation.Binary.Construct.Union as Union using (_∪_)
open import Relation.Binary.Construct.Closure.Transitive as TransClosure
import Relation.Binary.Construct.NonStrictToStrict as NonStrictToStrict
open import Relation.Binary.PropositionalEquality
import Relation.Binary.Construct.Union as Union
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Nullary.Decidable using (False; fromWitnessFalse)

open import RoutingLib.Data.Sum
open import RoutingLib.Data.Fin using (_+ₘ_; _-ₘ_)
open import RoutingLib.Data.FiniteSet renaming (FiniteSet to FiniteSet⁺)
open import RoutingLib.Relation.Nullary.Finite.List.Setoid using (Finite)
open import RoutingLib.Relation.Nullary.Finite.List.Setoid.Properties using (Finite⇒Finiteₛ)
open import RoutingLib.Data.Maybe.Properties
open import RoutingLib.Relation.Binary using (StrictMinimum)
import RoutingLib.Relation.Binary.Construct.Closure.Transitive.Finite as TransClosure
import RoutingLib.Relation.Binary.Construct.Closure.Transitive as TransClosure
open import RoutingLib.Relation.Binary.Construct.Closure.Transitive.Any

open import RoutingLib.Routing.Basics.Network using (AdjacencyMatrix)
open import RoutingLib.Routing.Algebra

module RoutingLib.Routing.VectorBased.Asynchronous.Convergence.Step1_FreeImpliesERO
  {a b ℓ} {algebra : RawRoutingAlgebra a b ℓ}
  (isRoutingAlgebra : IsRoutingAlgebra algebra)
  {n} (A : AdjacencyMatrix algebra n)
  where

open RawRoutingAlgebra algebra
open IsRoutingAlgebra isRoutingAlgebra

open import RoutingLib.Routing.Prelude algebra n
open import RoutingLib.Routing.Basics.Assignment algebra n as Assignment
open import RoutingLib.Routing.Basics.Assignment.Properties isRoutingAlgebra n
open import RoutingLib.Routing.Basics.Network.Cycles algebra
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
    x y : Assignment

--------------------------------------------------------------------------------
-- An ordering over assignments
--------------------------------------------------------------------------------
-- In order to build a height function all we need to have is a
-- strict partial order over assignments with the property `x < Aᵢⱼ(x)`. When
-- the algebra is strictly increasing, one can simply use the ordering `_<ₐₚ_`
-- which compares the path-weights of the assignments and ignores the nodes.

-- However when the network is cycle free we must come up with something more
-- complicated. The hard part is proving that any such order is irreflexive, i.e.
-- it has no cycles in it.

-- The relation below is a generalisation of the dispute digraph. It says that
-- path-weight `x` is less than path-weight `y` if there exists some path of
-- either `<₊ = is preferred to` or `↝ = can be extended to` relations between
-- them. It is more general than the dispute digraph as used by both Griffin and
-- Sobrinho, as a) it only requires assignments (i.e. node + path-weight) rather
-- than couples (i.e. path + path-weight) and b) it weakens distributivity
-- violation links to merely `can be extended to` links.

infix 4 _<ᶠ_

_<ᶠ_ : Rel Assignment (a ⊔ ℓ)
_<ᶠ_ = TransClosure (_<ₐₚ_ ∪ _↝[ A ]_)

-- Predicates stating whether a path contains any extensions

↝∈_ : x <ᶠ y → Set _
↝∈_ = AnyEdge IsInj₂

↝∉_ : x <ᶠ y → Set _
↝∉ x = ¬ (↝∈ x)

-- It's decidable if a path contains any extensions

↝∈?_ : (x<ᶠy : x <ᶠ y) → Dec (↝∈ x<ᶠy)
↝∈?_ = anyEdge? isInj₂?

-- If the set of extended assignments are empty then the first assignment in the
-- path must be strictly preferred to the last assignment in the path.
↝∉⇒x<₊y : (x<y : x <ᶠ y) → ↝∉ x<y → x <ₐₚ y
↝∉⇒x<₊y [ inj₁ x<y ]     _  = x<y
↝∉⇒x<₊y [ inj₂ x<y ]     ↝∉ = contradiction (here₁ _) ↝∉
↝∉⇒x<₊y (inj₁ x<y ∷ y<z) ↝∉ = <ₐₚ-trans x<y (↝∉⇒x<₊y y<z (↝∉ ∘ there))
↝∉⇒x<₊y (inj₂ x↝y ∷ y<z) ↝∉ with ↝∈? y<z
... | no _  = contradiction (here₂ _) ↝∉
... | yes _ = contradiction (here₂ _) ↝∉

-- Given two related assignments, i.e. path through this graph, we identify the set
-- of assignments that are extended. If extensions exist in the path we return
-- nothing, otherwise we return a non-empty set of assignments.
extensions : (x<ᶠy : x <ᶠ y) → ↝∈ x<ᶠy → FiniteSet⁺ Assignment
extensions {x} [ inj₁ x<y ]      (here₁ ())
extensions {x} [ inj₂ x↝y ]      _          = ⟦ x ⟧
extensions {x} (inj₁ x<z ∷ z<ᶠy) (there ↝∈) = extensions z<ᶠy ↝∈ 
extensions {x} (inj₂ x↝z ∷ z<ᶠy) _          with ↝∈? z<ᶠy
... | no  _   = ⟦ x ⟧
... | yes ext = ⟦ x ⟧∪ extensions z<ᶠy ext

-- If some assignment `v` is preferred to the start point of the path then `v` must also
-- be preferred to the first extended assignment in the path (if it exists).
v≤x⇒v≤e[x<ᶠy]₀ : ∀ {v} → v ≤ₐₚ x → (x<ᶠy : x <ᶠ y) → (↝∈x<y : ↝∈ x<ᶠy) →
                 v ≤ₐₚ first (extensions x<ᶠy ↝∈x<y)
v≤x⇒v≤e[x<ᶠy]₀ v≤x [ inj₁ _ ]        (here₁ ()) 
v≤x⇒v≤e[x<ᶠy]₀ v≤x [ inj₂ _ ]        _          = v≤x
v≤x⇒v≤e[x<ᶠy]₀ v≤x (inj₁ x<z ∷ z<ᶠy) (there ↝∈) = v≤x⇒v≤e[x<ᶠy]₀ (≤ₐₚ-trans v≤x (proj₁ x<z)) z<ᶠy ↝∈
v≤x⇒v≤e[x<ᶠy]₀ v≤x (inj₂ x↝z ∷ z<ᶠy) _          with ↝∈? z<ᶠy
... | no  _ = v≤x
... | yes _ = v≤x

-- If the end point of the path is preferred to some assignment `v` then last extended assignment
-- in the path (if it exists) must be dominated by `v`.
y≤v⇒e[x<ᶠy]₋₁⊴v : ∀ {v} → y ≤ₐₚ v → (x<ᶠy : x <ᶠ y) → (↝∈x<y : ↝∈ x<ᶠy) →
                   last (extensions x<ᶠy ↝∈x<y) ⊴[ A ] v
y≤v⇒e[x<ᶠy]₋₁⊴v y≤v [ inj₁ x<y ]      (here₁ ()) 
y≤v⇒e[x<ᶠy]₋₁⊴v y≤v [ inj₂ x↝y ]      _          = ↝∧≤ₐₚ⇒⊴ A x↝y y≤v
y≤v⇒e[x<ᶠy]₋₁⊴v y≤v (inj₁ x<z ∷ z<ᶠy) (there ↝∈) = y≤v⇒e[x<ᶠy]₋₁⊴v y≤v z<ᶠy ↝∈
y≤v⇒e[x<ᶠy]₋₁⊴v y≤v (inj₂ x↝w ∷ w<ᶠy) _          with ↝∈? w<ᶠy
... | no  ↝∉w<ᶠy = ↝∧≤ₐₚ⇒⊴ A x↝w (≤ₐₚ-trans (proj₁ (↝∉⇒x<₊y w<ᶠy ↝∉w<ᶠy)) y≤v)
... | yes ↝∈w<ᶠy = y≤v⇒e[x<ᶠy]₋₁⊴v y≤v w<ᶠy ↝∈w<ᶠy

-- The iᵗʰ extended assignment in the path is threatened by i+1ᵗʰ extended assignment in the path
⟦y<ᶠz⟧↝ᵢ⊴⟦y<ᶠz⟧↝ᵢ₊₁ : (x<ᶠy : x <ᶠ y) (↝∈x<y : ↝∈ x<ᶠy) →
                      let e = extensions x<ᶠy ↝∈x<y in
                      ∀ i → iᵗʰ e (inject₁ i) ⊴[ A ] iᵗʰ e (suc i)
⟦y<ᶠz⟧↝ᵢ⊴⟦y<ᶠz⟧↝ᵢ₊₁ [ inj₁ _ ]         (here₁ ())
⟦y<ᶠz⟧↝ᵢ⊴⟦y<ᶠz⟧↝ᵢ₊₁ [ inj₂ _ ]         _          = λ()
⟦y<ᶠz⟧↝ᵢ⊴⟦y<ᶠz⟧↝ᵢ₊₁ (inj₁ x≤z ∷ z<ᶠy)  (there ↝∈) = ⟦y<ᶠz⟧↝ᵢ⊴⟦y<ᶠz⟧↝ᵢ₊₁ z<ᶠy ↝∈
⟦y<ᶠz⟧↝ᵢ⊴⟦y<ᶠz⟧↝ᵢ₊₁ {x} {y} (_∷_ {y = z} (inj₂ x↝z) z<ᶠy) _ with ↝∈? z<ᶠy
... | no  ↝∉z<ᶠy = λ()
... | yes ↝∈z<ᶠy = λ
  { 0F      → ↝∧≤ₐₚ⇒⊴ A x↝z (v≤x⇒v≤e[x<ᶠy]₀ ≤ₐₚ-refl z<ᶠy ↝∈z<ᶠy)
  ; (suc i) → ⟦y<ᶠz⟧↝ᵢ⊴⟦y<ᶠz⟧↝ᵢ₊₁ z<ᶠy ↝∈z<ᶠy i
  }

module MakeCycle (x<ᶠy : x <ᶠ y) (↝∈x<ᶠy : ↝∈ x<ᶠy) where
  assignments : FiniteSet⁺ Assignment
  assignments = extensions x<ᶠy ↝∈x<ᶠy
  
  m : ℕ
  m = FiniteSet⁺.n assignments
  
  nodes : Vector Node (suc m)
  nodes = proj₁ ∘ content assignments
  
  weights : Vector PathWeight (suc m)
  weights i = proj₂ (content assignments i)

  cycle : Cycle
  cycle = m , nodes

  nonFree : x ≈ₐ y → ∀ i → content assignments (i -ₘ 1) ⊴[ A ] content assignments i
  nonFree x≈y (suc i) = ⟦y<ᶠz⟧↝ᵢ⊴⟦y<ᶠz⟧↝ᵢ₊₁ x<ᶠy ↝∈x<ᶠy i
  nonFree x≈y 0F      = ⊴∧≤ₐₚ⇒⊴ A ⟦x<ᶠy⟧₋₁⊴x x≤⟦x<ᶠy⟧₀
    where
    ⟦x<ᶠy⟧₋₁⊴x = y≤v⇒e[x<ᶠy]₋₁⊴v ≤ₐₚ-refl x<ᶠy ↝∈x<ᶠy
    x≤⟦x<ᶠy⟧₀  = v≤x⇒v≤e[x<ᶠy]₀ (≤ₐₚ-reflexive (≈ₐ-sym x≈y)) x<ᶠy ↝∈x<ᶠy


-- When the topology is cycle free then irreflexivity can now be proved. This follows
-- as if the start point of the path is equal to the end point then:
--   ∙ if the path contains no extensions then x ≈ y and x <₊ y which is contradiction
--     by the irreflexivity of _<₊_
--   ∙ if the path does contain extensions then the set of extended assignments must form
--     a cycle thanks to x ≈ y and the previous lemmas.
.<ᶠ-irrefl : IsFreeAdjacencyMatrix A → Irreflexive _≈ₐ_ _<ᶠ_
<ᶠ-irrefl cf x≈y x<ᶠy with ↝∈? x<ᶠy
... | no  ↝∉x<ᶠy = <ₐₚ-irrefl x≈y (↝∉⇒x<₊y x<ᶠy ↝∉x<ᶠy)
... | yes ↝∈x<ᶠy = cf cycle (weights , nonFree x≈y)
  where open MakeCycle x<ᶠy ↝∈x<ᶠy

<ᶠ-trans : Transitive _<ᶠ_
<ᶠ-trans = TransClosure.trans

<ᶠ-respʳ-≈ : _<ᶠ_ Respectsʳ _≈ₐ_
<ᶠ-respʳ-≈ = TransClosure.R⁺-respʳ-≈ (Union.respʳ _<ₐₚ_ _↝[ A ]_ <ₐₚ-respʳ-≈ₐ (↝-respʳ-≈ₐ {A}))

<ᶠ-respˡ-≈ : _<ᶠ_ Respectsˡ _≈ₐ_
<ᶠ-respˡ-≈ = TransClosure.R⁺-respˡ-≈ (Union.respˡ _<ₐₚ_ _↝[ A ]_ <ₐₚ-respˡ-≈ₐ (↝-respˡ-≈ₐ {A}))

<ᶠ-resp-≈ : _<ᶠ_ Respects₂ _≈ₐ_
<ᶠ-resp-≈ = <ᶠ-respʳ-≈ , <ᶠ-respˡ-≈

<ᶠ-dec : Finite S → Decidable _<ᶠ_
<ᶠ-dec fin = TransClosure.R⁺? {S = 𝔸ₛ} (Finite⇒Finiteₛ (Assignment.finite fin)) 
  (Union.resp₂ <ₐₚ-resp-≈ₐ ↝-resp-≈ₐ)
  (Union.decidable _<ₐₚ?_ _↝[ A ]?_)

-- And importantly `x` is strictly less than `Aᵢⱼ(x)` even though the algebra
-- is not necessarily strictly increasing.
↝⇒<ᶠ : ∀ {x y} → x ↝[ A ] y → x <ᶠ y
↝⇒<ᶠ x↝y = [ inj₂ x↝y ]

<ₐₚ⇒<ᶠ : ∀ {a b} → a <ₐₚ b → a <ᶠ b
<ₐₚ⇒<ᶠ a<b = [ inj₁ a<b ]

<ᶠ-extensionRespectingOrder : IsFinite algebra → .(IsFreeAdjacencyMatrix A) → ExtensionRespectingOrder _ _
<ᶠ-extensionRespectingOrder fin cf = record
  { _<ᵣ_        = _<ᶠ_
  ; <ᵣ-irrefl   = <ᶠ-irrefl cf
  ; <ᵣ-trans    = <ᶠ-trans
  ; ↝⇒<ᵣ        = ↝⇒<ᶠ
  ; <ₐₚ⇒<ᵣ      = <ₐₚ⇒<ᶠ
  ; _<ᵣ?_       = <ᶠ-dec fin
  ; <ᵣ-respʳ-≈ₐ = <ᶠ-respʳ-≈
  ; <ᵣ-respˡ-≈ₐ = <ᶠ-respˡ-≈
  }
