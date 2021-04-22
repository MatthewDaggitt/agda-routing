
open import Data.Fin.Base using (Fin; zero; suc; _<_; inject₁; lower₁; toℕ; fromℕ)
open import Data.Fin.Properties as Fin using (all?; toℕ-inject₁)
open import Data.Fin.Patterns
open import Data.Fin.Induction using (<-wellFounded; Acc; acc)
open import Data.Nat.Base using (ℕ; suc; s≤s; NonZero)
open import Data.Nat.Properties as ℕ using (≤-reflexive)
open import Data.Product using (∃; _×_; _,_; proj₁; proj₂)
open import Data.Vec.Functional using (Vector)
open import Function using (flip)
open import Level using (0ℓ; _⊔_)
open import Relation.Binary hiding (Universal)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Negation using (¬?; contradiction)
open import Relation.Unary using (Pred; Universal)
open import Relation.Binary.PropositionalEquality using (refl)

open import RoutingLib.Data.Fin using (_+ₘ_; _-ₘ_)
open import RoutingLib.Data.Fin.Induction
open import RoutingLib.Iteration.Asynchronous.Dynamic.Schedule using (Epoch)

open import RoutingLib.Routing.Algebra
import RoutingLib.Routing.Basics.Assignment.Properties as AssignmentProperties

module RoutingLib.Routing.Basics.Network.Cycles
  {a b ℓ} (algebra : RawRoutingAlgebra a b ℓ)
  {n : ℕ}
  where

open RawRoutingAlgebra algebra
open import RoutingLib.Routing.Basics.Node n
open import RoutingLib.Routing.Basics.Assignment algebra n
open import RoutingLib.Routing.Basics.Network algebra n
open import RoutingLib.Routing.Basics.Network.Participants algebra

--------------------------------------------------------------------------------
-- Definitions

-- A cycle (v₁ , v₂ , ... , vₘ , v₁) is a non-empty finite set of nodes such
-- that the last node equals the first node.

-- Note that we don't expicitly store the redundant last node.

Cycle : Set
Cycle = ∃ λ m → Vector Node (suc m)

-- A cycle (v₁ , v₂ , ... , vₘ , v₁) is non-free with respect to an adjacency
-- matrix if there exists a set of path-weights (x₁ , x₂ , ... , xₘ , x₁) such
-- that for all i, the assignment (u i , x i) threatens the assignment
-- (u i , x i). i.e. if every path-weight in the set threatens the adoption of
-- the previous path-weight in the set.

IsNonFreeCycle : AdjacencyMatrix → Cycle → Set (a ⊔ ℓ)
IsNonFreeCycle A (m , C) = ∃ λ (X : Vector PathWeight (suc m)) →
  ∀ i → (C (i -ₘ 1) , X (i -ₘ 1)) ⊴[ A ] (C i , X i)

IsFreeCycle : AdjacencyMatrix → Cycle → Set (a ⊔ ℓ)
IsFreeCycle A C = ¬ IsNonFreeCycle A C

-- An adjacency matrix is cycle free if there exists no set of
-- assignments that is cyclic.
IsFreeAdjacencyMatrix : (A : AdjacencyMatrix) → Set (a ⊔ ℓ)
IsFreeAdjacencyMatrix A = ∀ (C : Cycle) → IsFreeCycle A C

-- A network is free during an epoch and set of participants if the
-- resulting participation topology is free

TopologyIsFree : Network → Epoch × Participants → Set (a ⊔ ℓ)
TopologyIsFree N (e , p) = IsFreeAdjacencyMatrix (Aₜ N e p)

AllLinksEqual : AdjacencyMatrix → Cycle → Set (a ⊔ ℓ)
AllLinksEqual A (m , C) = ∃ λ x → x ≉ ∞# × ∀ i → A (C i) (C (i -ₘ 1)) ▷ x ≈ x

--------------------------------------------------------------------------------
-- Properties

module _ (isRoutingAlgebra : IsRoutingAlgebra algebra) where

  open IsRoutingAlgebra
  open AssignmentProperties isRoutingAlgebra n
  open import RoutingLib.Routing.Algebra.Properties.RoutingAlgebra isRoutingAlgebra
  open import Relation.Binary.Reasoning.PartialOrder ≤₊-poset
  open import RoutingLib.Routing.Algebra.Consequences isRoutingAlgebra
{-
Cyclic? : Decidable Cyclic
Cyclic? A (⟦ _ ∣ X ⟧) = all? (λ i → X (i -ₘ 1) ⊴? (X i))
  where open AdjacencyMatrixRelations algebra A
-}

--------------------------------------------------------------------------------
-- Relationship between increasing algebras and cycle-free topologies

  equalLinks⇒nonFree : (A : AdjacencyMatrix) (C : Cycle) →
                       AllLinksEqual A C → IsNonFreeCycle A C
  equalLinks⇒nonFree A (_ , C) (x , x≉∞ , A▷x≈x) =
    (λ _ → x) ,
    (λ i → x , (A▷x≈x i , x≉∞) , ≤₊-refl)
  
  incr∧nonFree⇒equalLinks : IsIncreasing algebra →
                            (A : AdjacencyMatrix) (C : Cycle) →
                            IsNonFreeCycle A C → AllLinksEqual A C
  incr∧nonFree⇒equalLinks incr A (m , C) (X , Cᵢ₋₁⊴Cᵢ) = x , x≉∞ , A▷x≈x
    where
    x : PathWeight
    x = X (0F -ₘ 1)

    x≉∞ : x ≉ ∞#
    x≉∞ = proj₂ (proj₁ (proj₂ (Cᵢ₋₁⊴Cᵢ 0F)))

    X₋₁≤X₀ : x ≤₊ X 0F
    X₋₁≤X₀ = incr∧⊴⇒≤₊ incr A (C 0F , _) (Cᵢ₋₁⊴Cᵢ 0F)

    x≤Xᵢ : ∀ i → x ≤₊ X i
    x≤Xᵢ = <-weakInduction _ X₋₁≤X₀ ind
      where
      ind : ∀ i → x ≤₊ X (inject₁ i) → x ≤₊ X (suc i)
      ind i x≤Xᵢ = begin
        x             ≤⟨ x≤Xᵢ ⟩
        X (inject₁ i) ≤⟨ incr∧⊴⇒≤₊ incr A (C (suc i) , _) (Cᵢ₋₁⊴Cᵢ (suc i)) ⟩
        X (suc i)     ∎

    Xᵢ≤x : ∀ i → X i ≤₊ x
    Xᵢ≤x = >-weakInduction _ ≤₊-refl ind
      where
      ind : ∀ i → X (suc i) ≤₊ x → X (inject₁ i) ≤₊ x
      ind i Xᵢ₊₁≤x = begin
        X (inject₁ i) ≤⟨ incr∧⊴⇒≤₊ incr A (C (suc i) , _) (Cᵢ₋₁⊴Cᵢ (suc i)) ⟩
        X (suc i)     ≤⟨ Xᵢ₊₁≤x ⟩
        x             ∎

    Xᵢ≈x : ∀ i → X i ≈ x
    Xᵢ≈x i = ≤₊-antisym (Xᵢ≤x i) (x≤Xᵢ i)
    
    A▷x≈x : ∀ i → A (C i) (C (i -ₘ 1)) ▷ x ≈ x
    A▷x≈x i = flip ≤₊-antisym (incr _ x) (begin
      A (C i) (C (i -ₘ 1)) ▷ x           ≈⟨ ▷-cong _ (≈-sym (Xᵢ≈x (i -ₘ 1))) ⟩
      A (C i) (C (i -ₘ 1)) ▷ X (i -ₘ 1)  ≤⟨ x⊴y⇒A▷x≤₊y A (Cᵢ₋₁⊴Cᵢ i) ⟩
      X i                                ≈⟨ Xᵢ≈x i ⟩
      x                                  ∎) 

  --------------------------------------------------------------------------------
  -- Relationship between strictly increasing algebras and cycle-free topologies

  -- If the algebra is strictly increasing then all adjacency matrices are
  -- guaranteed to be cycle free

  strIncr⇒¬equalLinks : IsStrictlyIncreasing algebra →
                        (A : AdjacencyMatrix) (C : Cycle) →
                        ¬ (AllLinksEqual A C)
  strIncr⇒¬equalLinks strIncr A (_ , C) (x , x≉∞ , A▷x≈x) =
    <₊-irrefl (≈-sym (A▷x≈x 0F)) (strIncr _ x≉∞)

  strIncr⇒freeAdjacencyMatrix : IsStrictlyIncreasing algebra →
                                (A : AdjacencyMatrix) → IsFreeAdjacencyMatrix A
  strIncr⇒freeAdjacencyMatrix strIncr A C nonFree = contradiction equalLinks ¬equalLinks
    where
    equalLinks : AllLinksEqual A C
    equalLinks = incr∧nonFree⇒equalLinks (strIncr⇒incr strIncr) A C nonFree

    ¬equalLinks : ¬ AllLinksEqual A C
    ¬equalLinks = strIncr⇒¬equalLinks strIncr A C
  {-
  allCycleFree⇒strIncr : (∀ {n} (A : AdjacencyMatrix n) → CycleFree A) →
                         IsStrictlyIncreasing algebra
  allCycleFree⇒strIncr cycleFree C x≉∞ = {!!}
  
  -- Conversely if all adjacency matrices are cycle free then the
  -- algebra is necessarily strictly increasing.

  allCycleFree⇒strIncr : (∀ {n} {i j : Fin n} → Step i j → Step j i) →
                         (∀ {n} (A : AdjacencyMatrix n) → CycleFree A) →
                         IsStrictlyIncreasing algebra
  allCycleFree⇒strIncr flip cycleFree {n} {i} {j} f {x} x≉∞ with f ▷ x ≤₊? x
  ... | no  fx≰x = ≰₊⇒>₊ fx≰x
  ... | yes fx≤x with f ▷ x ≟ ∞#
  ...   | yes fx≈∞ = <₊-respʳ-≈ (≈-sym fx≈∞) (<₊-maximum x≉∞)
  ...   | no  fx≉∞ = contradiction X-cyclic (cycleFree Aₓ X)
    where
    Aₓ : AdjacencyMatrix n
    Aₓ k l with k F.≟ i | l F.≟ j | k F.≟ j | l F.≟ i
    ... | yes refl | yes refl | _        | _        = f
    ... | _        | _        | yes refl | yes refl = flip f
    ... | _        | _        | _        | _        = f∞ k l

    Aₓᵢⱼ▷x≈f▷x : Aₓ i j ▷ x ≈ f ▷ x
    Aₓᵢⱼ▷x≈f▷x with i F.≟ i | j F.≟ j
    ... | yes refl | yes refl = ≈-refl
    ... | no  i≢i  | _        = contradiction refl i≢i
    ... | _        | no j≢j   = contradiction refl j≢j

    open Assignment algebra n

    X : FiniteSet⁺ Assignment
    X = ⟦ 1 ∣ (λ {0F → i , f ▷ x ; 1F → j , x}) ⟧

    X-cyclic : Cyclic Aₓ X
    X-cyclic 0F = (i , f ▷ x) , (x≉∞ , Aₓᵢⱼ▷x≈f▷x) , {!!}
    X-cyclic 1F = (j , flip f ▷ (f ▷ x)) , (fx≉∞ , {!!}) , {!!}
  -}
  ------------------------------------------------------------------------
  -- Free networks

  -- If the algebra is strictly increasing, then any network is free for
  -- every epoch and set of participants

  strIncr⇒alwaysFree : IsStrictlyIncreasing algebra →
                       (N : Network) → Universal (TopologyIsFree N)
  strIncr⇒alwaysFree strIncr N (e , p) = strIncr⇒freeAdjacencyMatrix strIncr (Aₜ N e p)
