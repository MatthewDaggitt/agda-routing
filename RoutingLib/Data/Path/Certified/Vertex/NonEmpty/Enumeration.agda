open import Data.Fin using (Fin; toℕ; fromℕ≤)
open import Data.Fin.Properties using (toℕ-fromℕ≤) renaming (_≟_ to _≟F_)
open import Data.Nat using (ℕ; zero; suc; _≤_; _<_)
open import Data.Nat.Properties using (<⇒≢; <⇒≤; ≤-reflexive)
open import Data.List using (List; []; _∷_; map; filter; concat; allFin; upTo; applyUpTo)
open import Data.List.Any using (here; there)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Setoid.Properties using (∈-map⁺; ∈-concat⁺′; ∈-applyUpTo⁺; ∈-resp-≈)
-- open import Data.List.All using (All; []; _∷_) renaming (map to mapₐ)
open import Data.List.All.Properties using (applyUpTo⁺₁; applyUpTo⁺₂; concat⁺)
open import Data.Product as Prod using (∃₂; ∃; _,_; _×_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary using (Setoid; DecSetoid; _Respects_)
open import Relation.Binary.List.Pointwise using () renaming (setoid to listSetoid)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; cong; cong₂; subst) renaming (setoid to ≡-setoid; refl to ≡-refl; sym to ≡-sym; trans to ≡-trans)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Function using (_∘_; id)

open import RoutingLib.Data.List using (allFinPairs)
open import RoutingLib.Data.List.Membership.Propositional.Properties using (∈-allFin⁺; ∈-combine⁺; ∈-allFinPairs⁺)
open import RoutingLib.Data.VertexPath.NonEmpty hiding (_∈_)
open import RoutingLib.Data.VertexPath.NonEmpty.All using (All; [_]; _∷_; All-resp-≈ₚ)
open import RoutingLib.Data.VertexPath.NonEmpty.Properties
open import RoutingLib.Data.VertexPath.NonEmpty.Relation.Equality renaming (ℙₛ to Pₛ)
open import RoutingLib.Data.VertexPath.NonEmpty.Finiteness using (|p|≤n)

module RoutingLib.Data.VertexPath.NonEmpty.Enumeration (n : ℕ) where

  -- Enumerating paths

  private

    Fₛ : Setoid _ _
    Fₛ = ≡-setoid (Fin n)

    ℕₛ : Setoid _ _
    ℕₛ = ≡-setoid ℕ
    
    F×Fₛ : Setoid _ _
    F×Fₛ = ≡-setoid (Fin n × Fin n)

    ℕ×ℕₛ : Setoid _ _
    ℕ×ℕₛ = ≡-setoid (ℕ × ℕ)
    
    LPₛ : Setoid _ _
    LPₛ = listSetoid Pₛ

    open import Data.List.Membership.Setoid Pₛ using () renaming (_∈_ to _∈ₚ_; _∉_ to _∉ₚ_)
    open import RoutingLib.Data.List.Relation.Disjoint   Pₛ using () renaming (_#_ to _#ₚ_)
    open import RoutingLib.Data.List.Uniqueness.Setoid Pₛ using () renaming (Unique to Uniqueₚ)
    open Setoid LPₛ using () renaming (reflexive to ≈ₗₚ-reflexive)





  abstract

    -- all arcs

    arcs : List ℕ
    arcs = upTo n

    ∈-arcs⁺ : ∀ {i} → i < n → i ∈ arcs
    ∈-arcs⁺ i<n = ∈-applyUpTo⁺ ℕₛ id i<n
    

    -- extensions
    
    extendAll : List Pathⁿᵗ → ℕ → List Pathⁿᵗ
    extendAll []       _ = []
    extendAll (p ∷ ps) i with i ∉? p
    ... | no  i∈p = extendAll ps i
    ... | yes i∉p = (i ∷ p ∣ i∉p) ∷ extendAll ps i

    ∈-extendAll : ∀ {i q e∉q ps} → q ∈ₚ ps → i ∷ q ∣ e∉q ∈ₚ extendAll ps i
    ∈-extendAll {i} {_} {i∉q} {p ∷ _} (here q≈p) with i ∉? p
    ... | no  i∈p = contradiction (∉-resp-≈ₚ q≈p i∉q) i∈p
    ... | yes i∉p = here (≡-refl ∷ q≈p)
    ∈-extendAll {i} {ps = p ∷ _} (there q∈ps) with i ∉? p
    ... | no  i∈p = ∈-extendAll q∈ps
    ... | yes i∉p = there (∈-extendAll q∈ps)

    extendAll-∈ : ∀ {i v} ps → v ∈ₚ extendAll ps i → ∃₂ λ q e∉q → v ≈ₚ i ∷ q ∣ e∉q
    extendAll-∈ []  ()
    extendAll-∈ {i} (p ∷ ps) v∈e[p∷ps] with i ∉? p
    ... | no  _   = extendAll-∈ ps v∈e[p∷ps]
    ... | yes e∉p with v∈e[p∷ps]
    ...   | here  v≈i∷p   = p , e∉p , v≈i∷p
    ...   | there v∈e[ps] = extendAll-∈ ps v∈e[ps]



  abstract

    allPathsOfLength : ℕ → List Pathⁿᵗ
    allPathsOfLength 0       = []
    allPathsOfLength 1       = map [_] arcs
    allPathsOfLength (suc l) = concat (map (extendAll (allPathsOfLength l)) arcs)

    ∈-allPathsOfLength : ∀ {p} → All (_< n) p → p ∈ₚ (allPathsOfLength (length p))
    ∈-allPathsOfLength {[ _ ]}       _           = {!!} --here ≈ₚ-refl
    ∈-allPathsOfLength {i ∷ p ∣ e∉p} (i<n ∷ p<n) = {!!}
    {-
      ∈-concat⁺′ Pₛ
        {vs  = extendAll (allPathsOfLength (length p)) i}
        {xss = map (extendAll (allPathsOfLength (length p))) arcs}
        (∈-extendAll (∈-allPathsOfLength p<n))
        (∈-map⁺ ℕₛ LPₛ
          (≈ₗₚ-reflexive ∘ cong (extendAll (allPathsOfLength (length p))))
          (∈-arcs⁺ i<n))
    -}
    
{-
    allPaths : List Pathⁿᵗ
    allPaths = ? ∷ concat (applyUpTo allPathsOfLength n)
    
    ∈-allPaths : ∀ {p} → All (_< n) p → p ∈ₚ allPaths
    ∈-allPaths {[]}          _   = here ≈ₚ-refl
    ∈-allPaths {i ∷ p ∣ i∉p} p<n =
      there (∈-concat⁺′ Pₛ
        (∈-allPathsOfLength p<n)
        (∈-applyUpTo⁺ LPₛ allPathsOfLength (|p|≤n p<n)))
-}
