open import Data.Fin using (Fin; toℕ; fromℕ≤)
open import Data.Fin.Properties using (toℕ-fromℕ≤) renaming (_≟_ to _≟F_)
open import Data.Nat using (ℕ; zero; suc; _≤_; _<_)
open import Data.Nat.Properties using (<⇒≢; <⇒≤; ≤-reflexive)
open import Data.List using (List; []; _∷_; map; filter; concat; allFin; applyUpTo)
open import Data.List.Any using (here; there)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Setoid.Properties using (∈-map⁺; ∈-concat⁺′; ∈-applyUpTo⁺; ∈-resp-≈)
open import Data.List.All using (All; []; _∷_) renaming (map to mapₐ)
open import Data.List.All.Properties using (applyUpTo⁺₁; applyUpTo⁺₂; concat⁺)
open import Data.Product as Prod using (∃₂; ∃; _,_; _×_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary using (Setoid; DecSetoid; _Respects_)
open import Relation.Binary.List.Pointwise using () renaming (setoid to listSetoid)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; cong; cong₂; subst) renaming (setoid to ≡-setoid; refl to ≡-refl; sym to ≡-sym; trans to ≡-trans)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Function using (_∘_)

open import RoutingLib.Data.List using (allFinPairs)
open import RoutingLib.Data.List.Membership.Propositional.Properties using (∈-allFin⁺; ∈-combine⁺; ∈-allFinPairs⁺)
open import RoutingLib.Data.Path.EdgePath.NonEmpty hiding (_∈_)
open import RoutingLib.Data.Path.EdgePath.NonEmpty.All
open import RoutingLib.Data.Path.EdgePath.NonEmpty.Properties
open import RoutingLib.Data.Path.EdgePath.NonEmpty.Relation.Equality renaming (ℙₛ to Pₛ)
open import RoutingLib.Data.Path.EdgePath.NonEmpty.Finiteness using (|p|<n; nonEmpty)

module RoutingLib.Data.Path.EdgePath.NonEmpty.Enumeration (n : ℕ) where

  -- Enumerating paths

  private

    Fₛ : Setoid _ _
    Fₛ = ≡-setoid (Fin n)

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

    arcs : List Edge
    arcs = map (Prod.map toℕ toℕ) (allFinPairs n)

    ∈-arcs⁺ : ∀ {i j} → i < n → j < n → (i , j) ∈ arcs
    ∈-arcs⁺ i<n j<n = subst (_∈ arcs) (arc-toFromℕ i<n j<n) (∈-map⁺ F×Fₛ ℕ×ℕₛ (λ { ≡-refl → ≡-refl }) (∈-allFinPairs⁺ _ _))
    

    -- extensions
    
    extendAll : List Pathⁿᵗ → Edge → List Pathⁿᵗ
    extendAll []       _       = []
    extendAll (p ∷ ps) (i , j) with (i , j) ⇿? p | i ∉? p
    ... | no  _   | _       = extendAll ps (i , j)
    ... | yes e⇿p | no  i∈p = extendAll ps (i , j)
    ... | yes e⇿p | yes i∉p = ((i , j) ∷ p ∣ e⇿p ∣ i∉p) ∷ extendAll ps (i , j)

    ∈-extendAll : ∀ {i j q e⇿q e∉q ps} → q ∈ₚ ps → (i , j) ∷ q ∣ e⇿q ∣ e∉q ∈ₚ extendAll ps (i , j)
    ∈-extendAll {i} {j} {_} {e⇿q} {i∉q} {p ∷ _} (here q≈p) with (i , j) ⇿? p | i ∉? p
    ... | no ¬e⇿p | _       = contradiction (⇿-resp-≈ₚ q≈p e⇿q) ¬e⇿p
    ... | yes e⇿p | no  i∈p = contradiction (∉-resp-≈ₚ q≈p i∉q) i∈p
    ... | yes e⇿p | yes i∉p = here (≡-refl ∷ q≈p)
    ∈-extendAll {i} {j} {ps = p ∷ _} (there q∈ps) with (i , j) ⇿? p | i ∉? p
    ... | no  _   | _       = ∈-extendAll q∈ps
    ... | yes e⇿p | no  i∈p = ∈-extendAll q∈ps
    ... | yes e⇿p | yes i∉p = there (∈-extendAll q∈ps)

    extendAll-∈ : ∀ {i j v} ps → v ∈ₚ extendAll ps (i , j) → ∃ λ q → ∃₂ λ e⇿q e∉q → v ≈ₚ (i , j) ∷ q ∣ e⇿q ∣ e∉q
    extendAll-∈ []  ()
    extendAll-∈ {i} {j} (p ∷ ps) v∈e[p∷ps] with (i , j) ⇿? p | i ∉? p
    ... | no  _   | _       = extendAll-∈ ps v∈e[p∷ps]
    ... | yes _   | no  _   = extendAll-∈ ps v∈e[p∷ps]
    ... | yes e⇿p | yes e∉p with v∈e[p∷ps]
    ...   | here  v≈i∷p   = p , e⇿p , e∉p , v≈i∷p
    ...   | there v∈e[ps] = extendAll-∈ ps v∈e[ps]



  abstract

    allPathsOfLength : ℕ → List Pathⁿᵗ
    allPathsOfLength 0       = [] ∷ []
    allPathsOfLength (suc l) = concat (map (extendAll (allPathsOfLength l)) arcs)

    ∈-allPathsOfLength : ∀ {p} → Allₙ (_< n) p → p ∈ₚ (allPathsOfLength (length p))
    ∈-allPathsOfLength {[]}                      _                    = here ≈ₚ-refl
    ∈-allPathsOfLength {(i , j) ∷ p ∣ e⇿p ∣ e∉p} ([ i<n , j<n ]∷ p<n) =
      ∈-concat⁺′ Pₛ
        {vs  = extendAll (allPathsOfLength (length p)) (i , j)}
        {xss = map (extendAll (allPathsOfLength (length p))) arcs}
        (∈-extendAll (∈-allPathsOfLength p<n))
        (∈-map⁺ ℕ×ℕₛ LPₛ
          (≈ₗₚ-reflexive ∘ cong (extendAll (allPathsOfLength (length p))))
          (∈-arcs⁺ i<n j<n))
        
    allPaths : List Pathⁿᵗ
    allPaths = [] ∷ concat (applyUpTo allPathsOfLength n)
    
    ∈-allPaths : ∀ {p} → Allₙ (_< n) p → p ∈ₚ allPaths
    ∈-allPaths {[]}                _ = here ≈ₚ-refl
    ∈-allPaths {e ∷ p ∣ e⇿p ∣ e∉p} p<n =
      there (∈-concat⁺′ Pₛ
        (∈-allPathsOfLength p<n)
        (∈-applyUpTo⁺ LPₛ allPathsOfLength (|p|<n p<n (nonEmpty e p e⇿p e∉p))))
