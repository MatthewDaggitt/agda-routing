open import Data.Fin using (Fin)
open import Data.Fin.Subset using (Subset; _∈_; _∉_; _∪_; Nonempty)
open import Data.Fin.Subset.Properties using (_∈?_)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-comm)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.List using (List)
open import Data.List.Relation.Unary.All using (lookup)
import Data.List.Extrema as Extrema
open import Relation.Unary using () renaming (_∈_ to _∈ᵤ_)
import Relation.Binary.Reasoning.PartialOrder as POR
open import Relation.Binary.PropositionalEquality
  using (refl; _≢_; subst)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Negation using (contradiction)

open import RoutingLib.Data.Matrix using (SquareMatrix)
open import RoutingLib.Data.Fin.Subset using (Nonfull)
open import RoutingLib.Data.Fin.Subset.Properties using (Nonfull-witness)
open import RoutingLib.Data.Fin.Subset.Cutset
open import RoutingLib.Data.List using (allFinPairs)
open import RoutingLib.Routing.Basics.Path.CertifiedI.All

open import RoutingLib.Routing.Algebra
open import RoutingLib.Routing.Prelude using (RoutingMatrix; AdjacencyMatrix)
import RoutingLib.Routing.VectorBased.Synchronous.PathVector.RateOfConvergence.Prelude as Prelude
import RoutingLib.Routing.VectorBased.Synchronous.PathVector.RateOfConvergence.Step1_NodeSets as Step1_NodeSets

module RoutingLib.Routing.VectorBased.Synchronous.PathVector.RateOfConvergence.Step2_ConvergedSubtree
  {a b ℓ n-1} {algebra : RawRoutingAlgebra a b ℓ}
  (isRoutingAlgebra    : IsRoutingAlgebra algebra)
  (isPathAlgebra       : IsCertifiedPathAlgebra algebra (suc n-1))
  (isIncreasing        : IsIncreasing algebra)
  (A : AdjacencyMatrix algebra (suc n-1))
  (X : RoutingMatrix   algebra (suc n-1))
  (j : Fin (suc n-1))
  (t-1 : ℕ)
  {C : Subset (suc n-1)}
  (j∈C : j ∈ C)
  (C-nonFull : Nonfull C)
  (open Step1_NodeSets isRoutingAlgebra isPathAlgebra A X j)
  (C⊆𝓒ₜ : ∀ {i} → i ∈ C → i ∈ᵤ 𝓒 (suc t-1))
  where

open Prelude isRoutingAlgebra isPathAlgebra A
open Notation X j

open Extrema ≤₊-totalOrder
open POR ≤₊-poset

private

  t : ℕ
  t = suc t-1

  e↷C⇒w[t+s]≡w[t] : ∀ {e} → e ↷ C → ∀ s → weightₑ (t + s) e ≈ weightₑ t e
  e↷C⇒w[t+s]≡w[t] (_ , k∈C) s = ▷-cong (A _ _) (proj₁ (C⊆𝓒ₜ k∈C) s)

------------------------------------------------------------------------------
-- Finding the fixed minimal edge entering the fixed set

-- At least one edge entering the fixed set exists

  eₐ : Edge
  eₐ = (proj₁ (Nonfull-witness C-nonFull) , j)

  eₐ↷C : eₐ ↷ C
  eₐ↷C = (proj₂ (Nonfull-witness C-nonFull) , j∈C)

-- We can therefore find the minimum weight edge out of the fixed set

abstract

  eₘᵢₙ : Edge
  eₘᵢₙ = argmin (weightₑ t) eₐ (cutset C)

  eₘᵢₙ↷C : eₘᵢₙ ↷ C
  eₘᵢₙ↷C = argmin-all (weightₑ t) eₐ↷C (∈cutset⇒↷ C)

iₘᵢₙ : Node
iₘᵢₙ = proj₁ eₘᵢₙ

iₘᵢₙ∉C : iₘᵢₙ ∉ C
iₘᵢₙ∉C = proj₁ eₘᵢₙ↷C

kₘᵢₙ : Node
kₘᵢₙ = proj₂ eₘᵢₙ

kₘᵢₙ∈C : kₘᵢₙ ∈ C
kₘᵢₙ∈C = proj₂ eₘᵢₙ↷C

------------------------------------------------------------------------------
-- Properties of eₘᵢₙ

abstract

  j≢iₘᵢₙ : j ≢ iₘᵢₙ
  j≢iₘᵢₙ j≡iₘᵢₙ = iₘᵢₙ∉C (subst (_∈ C) j≡iₘᵢₙ j∈C)

  kₘᵢₙ∈𝓒ₜ : kₘᵢₙ ∈ᵤ 𝓒 t
  kₘᵢₙ∈𝓒ₜ = C⊆𝓒ₜ kₘᵢₙ∈C

  -- Any edge that cuts the fixed set is -always- less than the minimum edge
  eₘᵢₙ-isMinₜ₊ₛ : ∀ {e} → e ↷ C → ∀ s →
                  weightₑ (t + s) eₘᵢₙ ≤₊ weightₑ (t + s) e
  eₘᵢₙ-isMinₜ₊ₛ {e} e↷C s = begin
    weightₑ (t + s) eₘᵢₙ  ≈⟨ e↷C⇒w[t+s]≡w[t] eₘᵢₙ↷C s ⟩
    weightₑ t       eₘᵢₙ  ≤⟨ lookup (f[argmin]≤f[xs] eₐ (cutset C)) (↷⇒∈cutset e↷C) ⟩
    weightₑ t       e     ≈⟨ ≈-sym (e↷C⇒w[t+s]≡w[t] e↷C s) ⟩
    weightₑ (t + s) e     ∎



-- Safe extension

  safe-extension : ∀ {s r i k l} → σ (t + r) X k j ≈ A k l ▷ (σ (t + s) X l j) →
                   eₘᵢₙ ≤[ t + s ] (k , l) → eₘᵢₙ ≤[ t + r ] (i , k)
  safe-extension {s} {r} {i} {k} {l} σ¹⁺ᵗ⁺ˢₖⱼ≈Aₖₗσᵗ⁺ˢₗⱼ eₘᵢₙ≤kl = (begin
    A iₘᵢₙ kₘᵢₙ ▷ σ (t + r) X kₘᵢₙ j   ≈⟨ ▷-cong (A iₘᵢₙ kₘᵢₙ) (𝓒-eq t kₘᵢₙ r s kₘᵢₙ∈𝓒ₜ) ⟩
    A iₘᵢₙ kₘᵢₙ ▷ σ (t + s) X kₘᵢₙ j   ≤⟨ eₘᵢₙ≤kl ⟩
    A k l ▷ σ (t + s) X l j           ≤⟨ isIncreasing (A i k) (A k l ▷ σ (t + s) X l j) ⟩
    A i k ▷ (A k l ▷ σ (t + s) X l j) ≈⟨ ▷-cong (A i k) (≈-sym σ¹⁺ᵗ⁺ˢₖⱼ≈Aₖₗσᵗ⁺ˢₗⱼ) ⟩
    A i    k   ▷ σ (t + r) X k   j    ∎)


------------------------------------------------------------------------------
-- Any "real" route ending in a node outside of the fixed set is worse
-- than that ending with the minimal edge.

∈𝓡-invalid : ∀ s {i k} →
                path (σ (t + s) X k j) ≈ₚ invalid →
                eₘᵢₙ ≤[ t + s ] (i , k)
∈𝓡-invalid s {i} {k} p[σᵗ⁺ˢXₖⱼ]≈∅ = begin
  A iₘᵢₙ kₘᵢₙ ▷ σ (t + s) X kₘᵢₙ j ≤⟨ ≤₊-maximum _ ⟩
  ∞#                               ≈⟨ ≈-sym (▷-fixedPoint (A i k)) ⟩
  A i    k    ▷ ∞#                 ≈⟨ ≈-sym (▷-cong (A i k) (path[r]≈∅⇒r≈∞ p[σᵗ⁺ˢXₖⱼ]≈∅)) ⟩
  A i    k    ▷ σ (t + s) X k j    ∎

∈𝓡-trivial : ∀ s {i k} → k ∉ C →
                path (σ (t + s) X k j) ≈ₚ valid [] →
                eₘᵢₙ ≤[ t + s ] (i , k)
∈𝓡-trivial s {i} {k} k∉C p[σᵗ⁺ˢXₖⱼ]≈[]
  with p[FXᵢⱼ]≈[]⇒i≡j (σ (t-1 + s) X) k j p[σᵗ⁺ˢXₖⱼ]≈[]
... | refl = contradiction j∈C k∉C

∈𝓡 : ∀ s i {k p} → path (σ (t + s) X k j) ≈ₚ p →
     k ∈ᵤ 𝓡 (t + s) → k ∉ C → 
     eₘᵢₙ ≤[ t + s ] (i , k)
∈𝓡 s i {_} {invalid}  p[σᵗ⁺ˢXₖⱼ]≈∅  _      _   = ∈𝓡-invalid s p[σᵗ⁺ˢXₖⱼ]≈∅
∈𝓡 s i {_} {valid []} p[σᵗ⁺ˢXₖⱼ]≈[] k∈Rₛ₊ₜ k∉C = ∈𝓡-trivial s k∉C p[σᵗ⁺ˢXₖⱼ]≈[]
∈𝓡 s i {_} {valid ((m , l) ∷ p ∣ _ ∣ _)} p[σᵗ⁺ˢXₖⱼ]≈kl∷p k∈Rₛ₊ₜ k∉C 
  with ∈𝓡 s m {_} {valid p} | 𝓡-path {t-1 + s} p[σᵗ⁺ˢXₖⱼ]≈kl∷p k∈Rₛ₊ₜ
... | rec | valid ([ _ , l∈Rₛ₊ₜ ]∷ _)
    with 𝓡-alignment (t-1 + s) k∈Rₛ₊ₜ p[σᵗ⁺ˢXₖⱼ]≈kl∷p
...   | refl , σᵗ⁺ˢXₖⱼ≈Aₖₗσᵗ⁺ˢXₗⱼ , p[σᵗ⁺ˢXₗⱼ]≈p with l ∈? C
...     | no  l∉C = safe-extension σᵗ⁺ˢXₖⱼ≈Aₖₗσᵗ⁺ˢXₗⱼ (rec p[σᵗ⁺ˢXₗⱼ]≈p l∈Rₛ₊ₜ l∉C )
...     | yes l∈C = safe-extension σᵗ⁺ˢXₖⱼ≈Aₖₗσᵗ⁺ˢXₗⱼ (eₘᵢₙ-isMinₜ₊ₛ (k∉C , l∈C) s)
