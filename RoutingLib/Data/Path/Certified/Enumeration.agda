open import Data.Fin using (Fin)
open import Data.Fin.Properties using () renaming (_≟_ to _≟F_)
open import Data.Nat using (ℕ; zero; suc; _≤_; _<_)
open import Data.Nat.Properties using (<⇒≢; <⇒≤; ≤-reflexive)
open import Data.List using (List; []; _∷_; map; filter; concat; allFin; applyUpTo)
open import Data.List.Any using (here; there)
open import Data.List.Membership.Propositional using (_∈_)
import Data.List.Membership.Setoid as Membership
open import Data.List.Membership.Setoid.Properties using (∈-map⁺; ∈-concat⁺′; ∈-applyUpTo⁺)
open import Data.List.All using (All; []; _∷_) renaming (map to mapₐ)
open import Data.List.All.Properties using (applyUpTo⁺₁; applyUpTo⁺₂; concat⁺)
open import Data.Product using (∃₂; ∃; _,_; _×_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary using (Setoid; DecSetoid; _Respects_)
open import Relation.Binary.List.Pointwise using () renaming (setoid to listSetoid)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; cong; cong₂; refl; setoid)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Function using (_∘_)

open import RoutingLib.Data.List using (allFinPairs)
open import RoutingLib.Data.List.Membership.Propositional.Properties using (∈-allFin⁺; ∈-combine⁺; ∈-allFinPairs⁺)

open import RoutingLib.Data.Path.Certified
open import RoutingLib.Data.Path.Certified.Properties


module RoutingLib.Data.Path.Certified.Enumeration (n : ℕ) where

  -- Enumerating paths

  private

    Eₛ : Setoid _ _
    Eₛ = 𝔼ₛ n

    Pₛ : Setoid _ _
    Pₛ = ℙₛ n

    LPₛ : Setoid _ _
    LPₛ = listSetoid Pₛ

    open Membership Pₛ using () renaming (_∈_ to _∈ₗ_)
    open Setoid LPₛ using () renaming (reflexive to ≈ₗₚ-reflexive)

  abstract

    extendAll : List (Path n) → Edge n → List (Path n)
    extendAll []       _       = []
    extendAll (p ∷ ps) (i , j) with (i , j) ⇿? p | i ∉ₚ? p
    ... | no  _   | _       = extendAll ps (i , j)
    ... | yes e⇿p | no  i∈p = extendAll ps (i , j)
    ... | yes e⇿p | yes i∉p = ((i , j) ∷ p ∣ e⇿p ∣ i∉p) ∷ extendAll ps (i , j)

    -- extensions

    ∈-extendAll : ∀ {e q e⇿q e∉q ps} → q ∈ₗ ps → (e ∷ q ∣ e⇿q ∣ e∉q) ∈ₗ extendAll ps e
    ∈-extendAll {i , j} {_} {e⇿q} {i∉q} {p ∷ _} (here q≈p) with (i , j) ⇿? p | i ∉ₚ? p
    ... | no ¬e⇿p | _       = contradiction (⇿-resp-≈ₚ q≈p e⇿q) ¬e⇿p
    ... | yes e⇿p | no  i∈p = contradiction (∉ₚ-resp-≈ₚ q≈p i∉q) i∈p
    ... | yes e⇿p | yes i∉p = here (refl ∷ q≈p)
    ∈-extendAll {i , j} {ps = p ∷ _} (there q∈ps) with (i , j) ⇿? p | i ∉ₚ? p
    ... | no  _   | _       = ∈-extendAll q∈ps
    ... | yes e⇿p | no  i∈p = ∈-extendAll q∈ps
    ... | yes e⇿p | yes i∉p = there (∈-extendAll q∈ps)

    extendAll-∈ : ∀ {e v} ps → v ∈ₗ extendAll ps e → ∃ λ q → ∃₂ λ e⇿q e∉q → v ≈ₚ e ∷ q ∣ e⇿q ∣ e∉q
    extendAll-∈ []  ()
    extendAll-∈ {i , j} (p ∷ ps) v∈e[p∷ps] with (i , j) ⇿? p | i ∉ₚ? p
    ... | no  _   | _       = extendAll-∈ ps v∈e[p∷ps]
    ... | yes _   | no  _   = extendAll-∈ ps v∈e[p∷ps]
    ... | yes e⇿p | yes e∉p with v∈e[p∷ps]
    ...   | here  v≈i∷p   = p , e⇿p , e∉p , v≈i∷p
    ...   | there v∈e[ps] = extendAll-∈ ps v∈e[ps]




  abstract

    allPathsOfLength : ℕ → List (Path n)
    allPathsOfLength 0       = [] ∷ []
    allPathsOfLength (suc l) = concat (map (extendAll (allPathsOfLength l)) (allFinPairs n))

    ∈-allPathsOfLength : ∀ p → p ∈ₗ (allPathsOfLength (length p))
    ∈-allPathsOfLength []                  = here ≈ₚ-refl
    ∈-allPathsOfLength ((i , j) ∷ p ∣ e⇿p ∣ e∉p) =
      ∈-concat⁺′ Pₛ
        (∈-extendAll (∈-allPathsOfLength p))
        (∈-map⁺ Eₛ LPₛ
          (≈ₗₚ-reflexive ∘ cong (extendAll (allPathsOfLength (length p))))
          (∈-allFinPairs⁺ i j))



    allPaths : List (Path n)
    allPaths = [] ∷ concat (applyUpTo allPathsOfLength n)

    ∈-allPaths : ∀ p → p ∈ₗ allPaths
    ∈-allPaths []                  = here ≈ₚ-refl
    ∈-allPaths (e ∷ p ∣ e⇿p ∣ e∉p) =
      there (∈-concat⁺′ Pₛ
        (∈-allPathsOfLength (e ∷ p ∣ e⇿p ∣ e∉p))
        (∈-applyUpTo⁺ LPₛ allPathsOfLength (|p|<n (nonEmpty e p e⇿p e∉p))))
