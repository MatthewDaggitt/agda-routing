--------------------------------------------------------------------------------
-- Agda routing library
--
-- This module defines the notion of a value of a path-weight being consistent
-- with the current network. This means that if you traversed the path along which
-- it claims it was generated along you would arrive at the same value. For
-- example a path-weight may be inconsistent with the current network topology
-- if a link on it's path has since failed or its weight has changed.
--
-- Using this notion it is possible to construct a new algebra using only
-- consistent path-weights.
--------------------------------------------------------------------------------

open import Algebra.Core  using (Op₂)
import Algebra.Definitions as AlgebraicDefinitions
open import Data.Fin as Fin using (Fin)
open import Data.List as List using (List; lookup)
import Data.List.Membership.Setoid as Membership
open import Data.List.Membership.Setoid.Properties using (∈-resp-≈; ∈-map⁺)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Nat using (suc)
open import Data.Product using (Σ; _×_; _,_; proj₁; map₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Vec.Functional using (Vector; map)
open import Function
open import Level using (_⊔_) renaming (zero to 0ℓ)
open import Relation.Binary as B hiding (Decidable)
open import Relation.Binary.PropositionalEquality
  using (inspect; [_]; _≡_; _≢_; refl; sym; trans; cong; module ≡-Reasoning)
import Relation.Binary.Construct.On as On
open import Relation.Unary as U hiding (Decidable; U)
open import Relation.Nullary using (¬_; yes; no; recompute)
open import Relation.Nullary.Negation using (contradiction)
import Relation.Binary.Reasoning.Setoid as SetoidReasoning

open import RoutingLib.Relation.Nullary.Decidable using (toSum)
open import RoutingLib.Relation.Nullary.Finite.List.Setoid.Properties
  using (Finite⇒Finiteₛ; via-dec-surjection)
open import RoutingLib.Data.FiniteSet using () renaming (FiniteSet to FiniteSet⁺)
open import RoutingLib.Data.Fin using (_-ₘ_)

open import RoutingLib.Routing.Basics.Path.CertifiedI
open import RoutingLib.Routing.Basics.Path.CertifiedI.Enumeration
open import RoutingLib.Routing.Basics.Path.CertifiedI.Properties
open import RoutingLib.Routing.Algebra
open import RoutingLib.Routing.Basics.Network
open import RoutingLib.Routing.Basics.Network.Cycles

module RoutingLib.Routing.Algebra.Construct.Consistent
  {a b ℓ n} {algebra : RawRoutingAlgebra a b ℓ}
  (isRoutingAlgebra : IsRoutingAlgebra algebra)
  (isPathAlgebra : IsCertifiedPathAlgebra algebra n)
  (A : AdjacencyMatrix algebra n)
  where

open RawRoutingAlgebra algebra
open IsRoutingAlgebra isRoutingAlgebra
open IsCertifiedPathAlgebra isPathAlgebra

open import RoutingLib.Routing.Algebra.Properties.CertifiedPathAlgebra isRoutingAlgebra isPathAlgebra
open import RoutingLib.Routing.Algebra.Properties.RoutingAlgebra isRoutingAlgebra
open import RoutingLib.Routing.Basics.Assignment algebra n

private
  variable
    i j : Fin n
    f : Step i j
    
--------------------------------------------------------------------------------
-- Definition
--------------------------------------------------------------------------------
-- A path-weight is consistent if it is equal to the weight of the path along
-- which it was generated.

𝑪 : PathWeight → Set ℓ
𝑪 r = weight A (path r) ≈ r

𝑰 : PathWeight → Set ℓ
𝑰 r = ¬ 𝑪 r

--------------------------------------------------------------------------------
-- Some simple properties

𝑪? : U.Decidable 𝑪
𝑪? r = weight A (path r) ≟ r

𝑪-cong : ∀ {r s} → r ≈ s → 𝑪 r → 𝑪 s
𝑪-cong r≈s rᶜ = ≈-trans (≈-trans (weight-cong (path-cong (≈-sym r≈s))) rᶜ) r≈s

𝑰-cong : ∀ {r s} → r ≈ s → 𝑰 r → 𝑰 s
𝑰-cong r≈s rⁱ sᶜ = rⁱ (𝑪-cong (≈-sym r≈s) sᶜ)

𝑪𝑰⇒≉ : ∀ {r s} → 𝑪 r → 𝑰 s → r ≉ s
𝑪𝑰⇒≉ rᶜ sⁱ r≈s = sⁱ (𝑪-cong r≈s rᶜ)

0ᶜ : 𝑪 0#
0ᶜ = weight-cong p[0]≈[]

∞ᶜ : 𝑪 ∞#
∞ᶜ = weight-cong p[∞]≈∅

⊕-pres-𝑪 : ∀ {r s} → 𝑪 r → 𝑪 s → 𝑪 (r ⊕ s)
⊕-pres-𝑪 {r} {s} rᶜ sᶜ with ⊕-sel r s
... | inj₁ r⊕s≈r = 𝑪-cong (≈-sym r⊕s≈r) rᶜ
... | inj₂ r⊕s≈s = 𝑪-cong (≈-sym r⊕s≈s) sᶜ

▷-pres-𝑪 : ∀ i j {r} → 𝑪 r → 𝑪 (A i j ▷ r)
▷-pres-𝑪 i j {r} rᶜ with p[f▷x]≈∅⊎↜ (A i j) r
... | inj₁ p[fx]≈∅ = 𝑪-cong (≈-sym (path[r]≈∅⇒r≈∞ p[fx]≈∅)) ∞ᶜ
... | inj₂ (q , p[x]≈q , ij⇿q , i∉q , p[fx]≈ij∷q) = begin
  weight A (path (A i j ▷ r))                  ≈⟨ weight-cong p[fx]≈ij∷q ⟩
  weight A (valid ((i , j) ∷ q ∣ ij⇿q ∣ i∉q))  ≡⟨⟩
  A i j ▷ weight A (valid q)                   ≈⟨ ▷-cong (A i j) (weight-cong (≈ₚ-sym p[x]≈q)) ⟩
  A i j ▷ weight A (path r)                    ≈⟨ ▷-cong (A i j) rᶜ ⟩ 
  A i j ▷ r                                    ∎
  where open SetoidReasoning S

▷-forces-𝑰 : ∀ {r} → 𝑰 (A i j ▷ r) → 𝑰 r
▷-forces-𝑰 f▷rⁱ rᶜ = f▷rⁱ (▷-pres-𝑪 _ _ rᶜ)

weightᶜ : ∀ p → 𝑪 (weight A p)
weightᶜ invalid                            = ∞ᶜ
weightᶜ (valid [])                         = 0ᶜ
weightᶜ (valid ((i , j) ∷ p ∣ e⇿p ∣ e∉p))  = ▷-pres-𝑪 i j (weightᶜ (valid p))

sizeⁱ-incr : ∀ {r} → 𝑰 (f ▷ r) → suc (size r) ≡ size (f ▷ r)
sizeⁱ-incr {i} {j} {f} {r} f▷rⁱ with p[f▷x]≈∅⊎↜ f r
... | inj₁ p[fx]≈∅ = contradiction (𝑪-cong (≈-sym (path[r]≈∅⇒r≈∞ p[fx]≈∅)) ∞ᶜ) f▷rⁱ
... | inj₂ (q , p[x]≈q , ij⇿q , i∉q , p[fx]≈ij∷q) = begin
  suc (length (path r))                     ≡⟨ cong suc (length-cong p[x]≈q) ⟩
  suc (length (valid q))                    ≡⟨⟩
  length (valid ((i , j) ∷ q ∣ ij⇿q ∣ i∉q)) ≡˘⟨ length-cong p[fx]≈ij∷q ⟩
  length (path (f ▷ r))                     ∎
  where open ≡-Reasoning

sizeⁱ-incr′ : ∀ {r s} → 𝑰 s → s ≈ f ▷ r → suc (size r) ≡ size s
sizeⁱ-incr′ sⁱ s≈f▷r = trans (sizeⁱ-incr (𝑰-cong s≈f▷r sⁱ)) (size-cong (≈-sym s≈f▷r))

recomputeᶜ : ∀ {x} → .(𝑪 x) → 𝑪 x
recomputeᶜ {x} = recompute (weight A (path x) ≟ x)

--------------------------------------------------------------------------------
-- The consistent routing algebra
--------------------------------------------------------------------------------
-- The subset of path-weights consistent with the current network topology form
-- a finite routing algebra

-- A consistent path-weight is simply a path-weight paired with a proof that it
-- iscconsistent.

record CPathWeight : Set (a ⊔ ℓ) where
  constructor _,_
  field
    pathWeight  : PathWeight
    .consistent : 𝑪 pathWeight

projᵣ : CPathWeight → PathWeight
projᵣ (x , _) = x

-- CPathWeight = Σ PathWeight 𝑪

toCPathWeight : ∀ {r} → 𝑪 r → CPathWeight
toCPathWeight {r} rᶜ = r , rᶜ

fromCPathWeight : CPathWeight → PathWeight
fromCPathWeight (r , _ ) = r

-- The sets of edge functions for the consistent routing algebra are a little
-- harder to define. The edges are labelled with the arcs, that are then
-- used to index into the current network topology. The problem is that they
-- technically they need to work for all sizes of networks. Therefore the
-- arc indexes (i.e. i and j from CStep i j) are discarded, and only the
-- contents of the arc (Fin n × Fin n) are used. The type has to be extended
-- to Maybe (Fin n × Fin n) to ensure that the algebra has an invalid edge f∞.
-- Finally to ensure that i and j are still inferable by Agda, it is made
-- into a record. Basically it's all an ugly hack but it seems to work.

record CStep {m} (i j : Fin m) : Set where
  constructor step
  field
    step : Maybe (Fin n × Fin n)

-- The trivial path-weight is simply taken from the original algebra

C0# : CPathWeight
C0# = 0# , 0ᶜ

-- The invalid path-weight is simply taken from the original algebra

C∞# : CPathWeight
C∞# = ∞# , ∞ᶜ

-- Equality over consistent path-weights is equality on the path-weight

infix 4 _≈ᶜ_ _≉ᶜ_ _≟ᶜ_

_≈ᶜ_ : Rel CPathWeight _
_≈ᶜ_ = _≈_ on projᵣ

_≉ᶜ_ : Rel CPathWeight _
r ≉ᶜ s = ¬ (r ≈ᶜ s)

-- Again the choice operator is simply lifted to consistent path-weights

infix 7 _⊕ᶜ_

_⊕ᶜ_ : Op₂ CPathWeight
(r , rᶜ) ⊕ᶜ (s , sᶜ) = r ⊕ s , ⊕-pres-𝑪 rᶜ sᶜ

-- Extension works a little differently. The arc containing `nothing` is the
-- invalid arc. For the arc (k , l), extending the path-weight is performed by
-- applying the original edge weight A k l in the network topology.

infix 6 _▷ᶜ_

_▷ᶜ_ : ∀ {n} {i j : Fin n} → CStep i j → CPathWeight → CPathWeight
(step nothing)         ▷ᶜ (r , rᶜ) = C∞#
(step (valid (k , l))) ▷ᶜ (r , rᶜ) = A k l ▷ r , ▷-pres-𝑪 k l rᶜ
-- As mentioned the invalid arc weight is simply `nothing`

f∞ᶜ : ∀ {n} (i j : Fin n) → CStep i j
f∞ᶜ i j = step nothing

-- As expected, equality obeys all the required properties

open AlgebraicDefinitions _≈ᶜ_

_≟ᶜ_ : B.Decidable _≈ᶜ_
_ ≟ᶜ _ = _ ≟ _

≈ᶜ-isDecEquivalence : IsDecEquivalence _≈ᶜ_
≈ᶜ-isDecEquivalence = On.isDecEquivalence projᵣ ≈-isDecEquivalence

Sᶜ : Setoid _ _
Sᶜ = On.setoid {B = CPathWeight} S projᵣ

DSᶜ : DecSetoid _ _
DSᶜ = On.decSetoid {B = CPathWeight} DS projᵣ

⊕ᶜ-cong : Congruent₂ _⊕ᶜ_
⊕ᶜ-cong = ⊕-cong

▷ᶜ-cong : ∀ {n} {i j : Fin n} (f : CStep i j) {r s} → r ≈ᶜ s → f ▷ᶜ r ≈ᶜ f ▷ᶜ s
▷ᶜ-cong (step nothing)         = λ _ → ≈-refl
▷ᶜ-cong (step (valid (k , l))) = ▷-cong (A k l)

f∞ᶜ-reject : ∀ {n} (i j : Fin n) → ∀ x → (f∞ᶜ i j) ▷ᶜ x ≈ᶜ C∞#
f∞ᶜ-reject _ _ _ = ≈-refl

-- Finally the raw routing algebra may be formed

algebraᶜ : RawRoutingAlgebra (a ⊔ ℓ) 0ℓ ℓ
algebraᶜ = record
  { PathWeight         = CPathWeight
  ; Step               = CStep
  ; _≈_                = _≈ᶜ_
  ; _⊕_                = _⊕ᶜ_
  ; _▷_                = _▷ᶜ_
  ; 0#                 = C0#
  ; ∞#                 = C∞#
  ; f∞                 = f∞ᶜ
  ; ≈-isDecEquivalence = ≈ᶜ-isDecEquivalence
  ; ⊕-cong             = ⊕-cong
  ; ▷-cong             = ▷ᶜ-cong
  ; f∞-reject          = f∞ᶜ-reject
  }

------------------------------------------------------------------------------
-- The consistent algebra obeys all the properties of a routing algebra

⊕ᶜ-assoc : Associative _⊕ᶜ_
⊕ᶜ-assoc _ _ _ = ⊕-assoc _ _ _

⊕ᶜ-comm : Commutative _⊕ᶜ_
⊕ᶜ-comm _ _ = ⊕-comm _ _

⊕ᶜ-sel : Selective _⊕ᶜ_
⊕ᶜ-sel _ _ = ⊕-sel _ _

⊕ᶜ-zeroʳ : RightZero C0# _⊕ᶜ_
⊕ᶜ-zeroʳ _ = ⊕-zeroʳ _

⊕ᶜ-identityʳ : RightIdentity C∞# _⊕ᶜ_
⊕ᶜ-identityʳ _ = ⊕-identityʳ _

▷ᶜ-fixedPoint : ∀ {n} {i j : Fin n} (f : CStep i j) → f ▷ᶜ C∞# ≈ᶜ C∞#
▷ᶜ-fixedPoint (step nothing)         = ≈-refl
▷ᶜ-fixedPoint (step (valid (k , l))) = ▷-fixedPoint (A k l)

isRoutingAlgebraᶜ : IsRoutingAlgebra algebraᶜ
isRoutingAlgebraᶜ = record
  { ⊕-sel        = ⊕ᶜ-sel
  ; ⊕-comm       = ⊕ᶜ-comm
  ; ⊕-assoc      = ⊕ᶜ-assoc
  ; ⊕-zeroʳ      = ⊕ᶜ-zeroʳ
  ; ⊕-identityʳ  = ⊕ᶜ-identityʳ
  ; ▷-fixedPoint = ▷ᶜ-fixedPoint
  }

------------------------------------------------------------------------------
-- There's a surjection between paths and consistent path-weights

fromPath : Path n → CPathWeight
fromPath p = weight A p , weightᶜ p

fromPath-surjective : Surjective (_≈ₚ_ {n = n}) _≈ᶜ_ fromPath
fromPath-surjective (y , yᶜ) = path y , recomputeᶜ yᶜ

fromPath-surjection : Surjection (ℙₛ n) Sᶜ
fromPath-surjection = record
  { f          = fromPath
  ; cong       = weight-cong
  ; surjective = fromPath-surjective
  }

------------------------------------------------------------------------------
-- The consistent algebra preserves strict increasingness and is always
-- guaranteed to be finite (as the set of simple paths in the network is
-- finite).

isIncreasingᶜ : IsIncreasing algebra → IsIncreasing algebraᶜ
isIncreasingᶜ incr (step (valid (k , l))) (r , _) = incr (A k l) r
isIncreasingᶜ incr (step nothing)         (r , _) = ≈-sym (⊕-identityˡ r)

isStrictlyIncreasingᶜ : IsStrictlyIncreasing algebra → IsStrictlyIncreasing algebraᶜ
isStrictlyIncreasingᶜ sIncr (step (valid (k , l)))     = sIncr (A k l)
isStrictlyIncreasingᶜ sIncr (step nothing)         r≉∞ = ≈-sym (⊕-identityˡ _) , r≉∞

isFiniteᶜ : IsFinite algebraᶜ
isFiniteᶜ = via-dec-surjection (finiteₗ n) DSᶜ fromPath-surjection

------------------------------------------------------------------------------
-- Finally the corresponding adjacency matrix for the consistent algebra may
-- be built and freeness of the topology is conserved.

Aᶜ : AdjacencyMatrix algebraᶜ n
Aᶜ i j = step (just (i , j))

nonFreeCycleᶜ : ∀ C → IsNonFreeCycle algebraᶜ Aᶜ C → IsNonFreeCycle algebra A C
nonFreeCycleᶜ (m , C) (pathWeightsᶜ , nonFreeᶜ) = map fromCPathWeight pathWeightsᶜ , nonFreeᶜ

freeᶜ : IsFreeAdjacencyMatrix algebra A → IsFreeAdjacencyMatrix algebraᶜ Aᶜ
freeᶜ cf C C-nonFree = cf C (nonFreeCycleᶜ C C-nonFree)

