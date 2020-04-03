--------------------------------------------------------------------------------
-- Agda routing library
--
-- This module (doesn't currently compile) contains some code for proving that
-- if the schedule is such that all nodes continue to activate and all links
-- continue to function then the schedule contains an infinite number of
-- pseudocycles.
--------------------------------------------------------------------------------

open import RoutingLib.Iteration.Asynchronous.Static.Schedule

module RoutingLib.Iteration.Asynchronous.Static.Schedule.Pseudocycle.Properties
  {n} (ψ : Schedule n) where

open import Data.Fin using (Fin; toℕ; fromℕ; inject≤; inject₁) renaming (zero to fzero)
open import Data.Fin.Properties using (inject≤-lemma; to-from; inject₁-lemma)
open import Data.Fin.Subset using (_∈_)
open import Data.Fin.Subset.Properties using (∈⊤)
open import Data.Fin.Dec using (_∈?_)
open import Data.Nat using (ℕ; zero; suc; _≤_; _<_; _⊔_; _∸_; _+_; z≤n; s≤s; _≟_; _≤?_; ≤-pred; less-than-or-equal)
open import Data.Nat.Properties using (m≤m⊔n; n≤1+n; ⊔-sel; module ≤-Reasoning; <-cmp; ≤+≢⇒<; <⇒≱; ≤-refl; <⇒≤; ⊔-identityʳ; <-irrefl; ≤-trans; ≤-reflexive; ≮⇒≥; n≤m⊔n; ⊔-mono-≤; m≤m+n; m+n∸m≡n; <⇒≢; ≤⇒≤″; +-suc; +-comm)
open import Data.Product using (∃; _,_; _×_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂; _⊎_)
open import Data.List using (List; []; _∷_; foldr; map; allFin; applyUpTo; tabulate)
open import Data.List.Any using (Any) renaming (map to anyMap)
open import Data.List.Any.Properties using (map⁺)
open import Data.List.Membership.Propositional.Properties using (∈-map⁺; ∈-applyUpTo⁺)
import Data.List.Extrema.Nat as List
import Data.List.Relation.Sublist.Propositional.Properties as Sublist
import Data.List.All as All
import Data.List.All.Properties as All
open import Data.Vec using (Vec; lookup) renaming (map to mapᵥ; allFin to allFinᵥ)
open import Function using (_∘_)
open import Induction.WellFounded using (Acc; acc)
open import Induction.Nat using () renaming (<-well-founded to <-wf)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary using (tri<; tri≈; tri>)
open import Relation.Binary.PropositionalEquality using (refl; sym; trans; cong; subst; _≢_; _≡_)

open import RoutingLib.Data.Nat.Properties using (m≤n⊎m≤o⇒m≤n⊔o; ∀x<m:n≢x⇒m≤n; n⊔m≡m⇒n≤m)
open import RoutingLib.Data.Vec.Functional using (max)
open import RoutingLib.Data.Vec.Functional.Properties using (t≤max[t]; x≤max[t]; max[s]≤max[t]; ⊥≤max[t])

import RoutingLib.Iteration.Asynchronous.Static.Schedule.Pseudocycle as Pseudocycle

open Schedule ψ
open Pseudocycle ψ

open ≤-Reasoning

-----------------
-- Finite --
-----------------
finite-fin : ∀ {t} k i j (t' : Fin (suc t)) →
            proj₁ (β-finite (toℕ t') i j) ≤ k →
            β k i j ≢ toℕ t'
finite-fin {t} k i j t' p  with finite (toℕ t') i j
... | (m , q) = subst (_≢ toℕ t')
  (cong (λ x → β x i j) (m+n∸m≡n p))
  (q (k ∸ m))

-----------------
-- Activations --
-----------------
-- Properties of nextActive'

nextActive'-active : ∀ t k {i} i∈α[t+1+k] rec → i ∈ α (nextActive' t k {i} i∈α[t+1+k] rec)
nextActive'-active t zero    {i} i∈α[t+1]  _       rewrite +-comm t 1 = i∈α[t+1]
nextActive'-active t (suc k) {i} i∈α[t+1+k] (acc rs) with i ∈? α t
... | yes i∈α                         = i∈α
... | no  i∉α rewrite +-suc t (suc k) = nextActive'-active (suc t) k i∈α[t+1+k] _

nextActive'-increasing : ∀ t k {i} i∈α[t+1+k] (acc : Acc _<_ k) →
                         t ≤ nextActive' t k {i} i∈α[t+1+k] acc
nextActive'-increasing t zero    {i} p _        = n≤1+n t
nextActive'-increasing t (suc k) {i} p (acc rec) with i ∈? α t
... | yes i∈α                         = ≤-reflexive refl
... | no  i∉α rewrite +-suc t (suc k) = begin
  t                         ≤⟨ n≤1+n t ⟩
  suc t                     ≤⟨ nextActive'-increasing (suc t) k p (rec k ≤-refl) ⟩
  nextActive' (suc t) k p _ ∎

-- Properties of nextActive

nextActive-increasing : ∀ t i → t ≤ nextActive t i
nextActive-increasing t i with nonstarvation t i
... | k , p = nextActive'-increasing t k p (<-wf k)

nextActive-active : ∀ t i → i ∈ α (nextActive t i)
nextActive-active t i with nonstarvation t i
... | (k , p) = nextActive'-active t k p (<-wf k)

-- Properties of allActive

allActive-increasing : ∀ t → t ≤ allActive t
allActive-increasing t = ⊥≤max[t] t (nextActive t)

nextActive≤allActive : ∀ t i → nextActive t i ≤ allActive t
nextActive≤allActive t i = t≤max[t] t _ i

---------------
-- Data flow --
---------------

-- Properties of pointExpiryᵢⱼ

pointExpiryᵢⱼ-expired : ∀ {i j t s} → pointExpiryᵢⱼ i j t ≤ s → β s i j ≢ t
pointExpiryᵢⱼ-expired {i} {j} {t} v≤s with ≤⇒≤″ v≤s
... | less-than-or-equal {k} refl = proj₂ (finite t i j) k

-- Properties of expiryᵢⱼ

expiryᵢⱼ-inc : ∀ t i j → t ≤ expiryᵢⱼ t i j
expiryᵢⱼ-inc t i j = List.⊥≤max t (applyUpTo (pointExpiryᵢⱼ i j) (suc t))

expiryᵢⱼ-monotone : ∀ {t k} → t ≤ k → ∀ i j → expiryᵢⱼ t i j ≤ expiryᵢⱼ k i j
expiryᵢⱼ-monotone t≤k i j = List.max-mono-⊆ t≤k (Sublist.applyUpTo⁺ (pointExpiryᵢⱼ i j) (s≤s t≤k))

pointExpiryᵢⱼ≤expiryᵢⱼ : ∀ t i j → pointExpiryᵢⱼ i j t ≤ expiryᵢⱼ t i j
pointExpiryᵢⱼ≤expiryᵢⱼ t i j = All.lookup (List.xs≤max t (applyUpTo (pointExpiryᵢⱼ i j) (suc t))) (∈-applyUpTo⁺ (pointExpiryᵢⱼ i j) ≤-refl)

expiryᵢⱼ-expired' : ∀ {t s r i j} → expiryᵢⱼ t i j ≤ s → r < t → β s i j ≢ r
expiryᵢⱼ-expired' {t} {s} {r} {i} {j} expiryₜᵢⱼ≤s βₛᵢⱼ<t refl =
  pointExpiryᵢⱼ-expired (begin
    pointExpiryᵢⱼ i j (β s i j) ≤⟨ pointExpiryᵢⱼ≤expiryᵢⱼ (β s i j) i j ⟩
    expiryᵢⱼ (β s i j) i j      ≤⟨ expiryᵢⱼ-monotone (<⇒≤ βₛᵢⱼ<t) i j ⟩
    expiryᵢⱼ t i j              ≤⟨ expiryₜᵢⱼ≤s ⟩
    s                           ∎) refl

expiryᵢⱼ-expired : ∀ {t k i j} → expiryᵢⱼ t i j ≤ k → t ≤ β k i j
expiryᵢⱼ-expired expiryᵢⱼt≤k = ∀x<m:n≢x⇒m≤n _ _ (expiryᵢⱼ-expired' expiryᵢⱼt≤k)

-- Properties of expiryᵢ

expiryᵢⱼ≤expiryᵢ : ∀ t i j → expiryᵢⱼ t i j ≤ expiryᵢ t i
expiryᵢⱼ≤expiryᵢ t i j = t≤max[t] t (expiryᵢⱼ t i) j

expiryᵢ-inc : ∀ t i → t ≤ expiryᵢ t i
expiryᵢ-inc t i = ⊥≤max[t] t (expiryᵢⱼ t i)

expiryᵢ-monotone : ∀ {t k} → t ≤ k → ∀ i → expiryᵢ t i ≤ expiryᵢ k i
expiryᵢ-monotone {t} {k} t≤k i = max[s]≤max[t] t (inj₁ t≤k)
                 (λ j → inj₂ (j , expiryᵢⱼ-monotone t≤k i j))

expiryᵢ-expired : ∀ {t k i} → expiryᵢ t i ≤ k → ∀ j → t ≤ β k i j
expiryᵢ-expired {t} {k} {i} expiryᵢt≤k j = expiryᵢⱼ-expired
                (≤-trans (expiryᵢⱼ≤expiryᵢ t i j) expiryᵢt≤k)


-- Properties of expiry

expiryᵢ≤expiry : ∀ t i → expiryᵢ t i ≤ expiry t
expiryᵢ≤expiry t i = t≤max[t] t (expiryᵢ t) i

expiry-increasing : ∀ t → t ≤ expiry t
expiry-increasing t = ⊥≤max[t] t (expiryᵢ t)

expiry-expired : ∀ {t k} → expiry t ≤ k → ∀ i j → t ≤ β k i j
expiry-expired {t} {k} expiryₜ≤k i j = expiryᵢ-expired (≤-trans (expiryᵢ≤expiry t i) expiryₜ≤k) j

expiry-monotone : ∀ {t k} → t ≤ k → expiry t ≤ expiry k
expiry-monotone {t} {k} t≤k = max[s]≤max[t] t {k} (inj₁ t≤k) (λ i → inj₂ (i , expiryᵢ-monotone t≤k i))

-------------------
-- Psuedo-cycles --
-------------------

-- Properties of φ
φ-increasing : ∀ K → K ≤ φ K
φ-increasing zero    = z≤n
φ-increasing (suc K) = s≤s (begin
  K                         ≤⟨ φ-increasing K ⟩
  φ K                       ≤⟨ allActive-increasing (φ K) ⟩
  allActive (φ K)           ≤⟨ expiry-increasing (allActive (φ K)) ⟩
  expiry (allActive (φ K))  ∎)

-- Properties of τ
τ-active :  ∀ K i → i ∈ α (τ K i)
τ-active K = nextActive-active (φ K)

τ-after-φ : ∀ K i → φ K ≤ τ K i
τ-after-φ zero     i = z≤n
τ-after-φ (suc K)  i = nextActive-increasing (φ (suc K)) i

τ-expired : ∀ K t i j → τ K j ≤ β (φ (suc K) + t) i j
τ-expired K t i j = expiry-expired (begin
  expiry (nextActive _ j)  ≤⟨ expiry-monotone (nextActive≤allActive (φ K) j) ⟩
  expiry (allActive (φ K)) ≤⟨ n≤1+n _ ⟩
  φ (suc K)                ≤⟨ m≤m+n (φ (suc K)) t ⟩
  φ (suc K) + t            ∎) i j

-- Every schedule is pseudoperiodic
isPseudoperiodic : IsPseudoperiodic 𝓢
isPseudoperiodic = record
  { φ                = φ
  ; τ                = τ
  ; φ-increasing     = φ-increasing
  ; τ-expired        = τ-expired
  ; τ-after-φ        = τ-after-φ
  ; τ-active         = τ-active
  }

pseudoperiodic : PseudoperiodicSchedule n
pseudoperiodic = record
  { 𝓢               = 𝓢
  ; isPseudoperiodic = isPseudoperiodic
  }
