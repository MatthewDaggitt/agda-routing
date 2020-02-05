------------------------------------------------------------------------
-- These are some internal definition used in the proof of convergence
------------------------------------------------------------------------

open import RoutingLib.Routing using (AdjacencyMatrix)
open import RoutingLib.Routing.Algebra

module RoutingLib.Routing.VectorBased.Asynchronous.Convergence.InternalDefinitions
  {a b ℓ} (algebra : RawRoutingAlgebra a b ℓ)
  {n} (A : AdjacencyMatrix algebra n)
  where

open RawRoutingAlgebra algebra

open import Data.Nat using (ℕ; _≤_; _<_)
open import Data.Product using (proj₁; proj₂)
open import Level
open import Relation.Binary
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Nullary using (¬_)

open import RoutingLib.Relation.Binary
open import RoutingLib.Function.Metric.Nat

open import RoutingLib.Routing.AdjacencyMatrix.Definitions algebra A
open import RoutingLib.Routing.VectorBased.Synchronous algebra A

------------------------------------------------------------------------
-- Building blocks

-- It occured to me (whilst programming dropdown boxes in Java) that what
-- determines whether or not we have a suitable height function on which our
-- entire proof in the SIGCOMM paper is based, is whether or not we have a
-- strict partial order over the routes which respects the extension,
-- i.e. x < Aᵢⱼ(x).

-- Obviously when the algebra is strictly contracting this is trivial and we
-- use _<₊_. However for free networks over non-strictly increasing algebras
-- we still get the strictly contracting part for free from _<₊_ and all we
-- have to do is tweak it to recover the `respect extensions` part. After
-- checking in Sobrinho's 2005 paper, the dispute digraph bit in the appendix
-- can easily be taken, generalised and then repurposed almost trivially.
-- I say trivial as it's only 8 small lemmas in Agda, which if that's not
-- trivial I'm not sure what is!

record IsExtensionRespectingOrder {ℓ₂} (_<ᵣ_ : Rel Route ℓ₂) : Set (a ⊔ ℓ ⊔ ℓ₂) where
  field
    isDecStrictPartialOrder : IsDecStrictPartialOrder _≈_ _<ᵣ_
    ↝⇒<ᵣ                    : _↝_ ⇒ _<ᵣ_
    <₊∧<ᵣ⇒<ᵣ                : Trans _<₊_ _<ᵣ_ _<ᵣ_
    <ᵣ-min                  : StrictMinimum _≈_ _<ᵣ_ 0#

  open IsDecStrictPartialOrder isDecStrictPartialOrder public
    renaming
    ( irrefl    to <ᵣ-irrefl
    ; trans     to <ᵣ-trans
    ; _<?_      to _<ᵣ?_
    ; <-respʳ-≈ to <ᵣ-respʳ-≈
    ; <-respˡ-≈ to <ᵣ-respˡ-≈
    )
    
record ExtensionRespectingOrder ℓ₂ : Set (a ⊔ ℓ ⊔ suc ℓ₂) where
  field
    _<ᵣ_                       : Rel Route ℓ₂
    isExtensionRespectingOrder : IsExtensionRespectingOrder _<ᵣ_

  open IsExtensionRespectingOrder isExtensionRespectingOrder public

------------------------------------------------------------------------
-- Height function

record HeightFunction : Set (a ⊔ ℓ) where
  field
    h         : Route → ℕ
    1≤h       : ∀ x → 1 ≤ h x
    h≤H       : ∀ x → h x ≤ h 0#
    h-resp-↝  : ∀ {x y} → x ↝  y → h y < h x
    h-resp-≤  : ∀ {x y} → x <₊ y → h y ≤ h x
    h-cong    : ∀ {x y} → x ≈  y → h x ≡ h y

  H : ℕ
  H = h 0#

------------------------------------------------------------------------
-- Route level distance function

record RouteDistanceFunction : Set (a ⊔ ℓ) where
  field
    r                   : Route → Route → ℕ
    r-isQuasiSemiMetric : IsQuasiSemiMetric _≈_ r 
    r-bounded           : Bounded r
    r-strContrOrbits    : ∀ {X v} → 0 < v → (∀ k l → r (X k l) (F X k l) ≤ v) →
                          ∀ i j → r (F X i j) (F (F X) i j) < v
    r-strContrFP        : ∀ {X*} → F X* ≈ₘ X* →
                          ∀ {X v} → 0 < v → (∀ k l → r (X* k l) (X k l) ≤ v) →
                          ∀ i j → r (X* i j) (F X i j) < v

  rₘₐₓ : ℕ
  rₘₐₓ = proj₁ r-bounded

  r≤rₘₐₓ : ∀ x y → r x y ≤ rₘₐₓ
  r≤rₘₐₓ = proj₂ r-bounded
  
  open IsQuasiSemiMetric r-isQuasiSemiMetric public
