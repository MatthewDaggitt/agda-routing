------------------------------------------------------------------------
-- These are some internal definition used in the proof of convergence
------------------------------------------------------------------------

open import Data.Nat using (ℕ; _≤_; _<_)
open import Data.Nat.Properties using (≤-totalOrder)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Fin using (Fin)
open import Data.Sum using (inj₂)
open import Function.Base using (_∘_)
open import Function.Metric.Nat
open import Level
open import Relation.Binary
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Nullary using (¬_)

open import RoutingLib.Relation.Binary
open import RoutingLib.Data.Vec.Functional
open import RoutingLib.Data.Vec.Functional.Properties

open import RoutingLib.Routing.Basics.Network using (AdjacencyMatrix)
open import RoutingLib.Routing.Algebra

module RoutingLib.Routing.VectorBased.Asynchronous.Convergence.Definitions
  {a b ℓ} (algebra : RawRoutingAlgebra a b ℓ)
  {n} (A : AdjacencyMatrix algebra n)
  where

open RawRoutingAlgebra algebra
open import RoutingLib.Routing.Basics.Assignment algebra n
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

-- This can't be defined in terms of IsDecStrictTotalOrder as we
-- need the irreflexive relation to irrelevant

record ExtensionRespectingOrder ℓ₂ : Set (a ⊔ ℓ ⊔ suc ℓ₂) where
  field
    _<ᵣ_         : Rel Assignment ℓ₂
    ↝⇒<ᵣ         : _↝[ A ]_ ⇒ _<ᵣ_
    <₊∧<ᵣ⇒<ᵣ     : Trans _<ₐₚ_ _<ᵣ_ _<ᵣ_
    ↝∧<ᵣ⇒<ᵣ      : Trans _↝[ A ]_  _<ᵣ_ _<ᵣ_
    .<ᵣ-irrefl   : Irreflexive _≈ₐ_ _<ᵣ_
    _<ᵣ?_        : Decidable _<ᵣ_
    <ᵣ-respʳ-≈ₐ  : _<ᵣ_ Respectsʳ _≈ₐ_
    <ᵣ-respˡ-≈ₐ  : _<ᵣ_ Respectsˡ _≈ₐ_
    <ᵣ-min       : ∀ {x y} → x <ᵣ y → (node x , 0#) <ᵣ y


  <ᵣ-resp₂-≈ₐ : ∀ {w x y z} → w ≈ₐ x → y ≈ₐ z → w <ᵣ y → x <ᵣ z
  <ᵣ-resp₂-≈ₐ w≈y y≈z = <ᵣ-respʳ-≈ₐ y≈z ∘ <ᵣ-respˡ-≈ₐ w≈y

------------------------------------------------------------------------
-- Height function

record HeightFunction : Set (a ⊔ ℓ) where
  field
    h         : Assignment → ℕ
    1≤h       : ∀ x → 1 ≤ h x
    h≤h[0]    : ∀ i x → h (i , x) ≤ h (i , 0#)
    h-resp-↝  : ∀ {x y} → x ↝[ A ] y → h y < h x
    h-resp-≤  : ∀ {x y} → x <ₐₚ y → h y ≤ h x
    h-cong    : ∀ {x y} → x ≈ₐ  y → h x ≡ h y
  
------------------------------------------------------------------------
-- Route level distance function

record RouteDistanceFunction : Set (a ⊔ ℓ) where
  field
    r                   : Node → Route → Route → ℕ
    r-isQuasiSemiMetric : ∀ i → IsQuasiSemiMetric _≈_ (r i) 
    r-bounded           : ∀ i → Bounded (r i)
    r-strContrOrbits    : ∀ {X v} → 0 < v → (∀ k l → r k (X k l) (F X k l) ≤ v) →
                          ∀ i j → r i (F X i j) (F (F X) i j) < v
    r-strContrFP        : ∀ {X*} → F X* ≈ₘ X* →
                          ∀ {X v} → 0 < v → (∀ k l → r k (X* k l) (X k l) ≤ v) →
                          ∀ i j → r i (X* i j) (F X i j) < v

  module _ (i : Node) where
    open IsQuasiSemiMetric (r-isQuasiSemiMetric i) public

  abstract
    rₘₐₓ : ℕ
    rₘₐₓ = max 0 (proj₁ ∘ r-bounded)

    r≤rₘₐₓ : ∀ i x y → r i x y ≤ rₘₐₓ
    r≤rₘₐₓ i x y = x≤max[t] 0 _ (inj₂ (i , proj₂ (r-bounded i) x y))
