open import Level using (_⊔_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Nullary using (yes; no)
open import Data.Product using (_×_; _,_)
open import Data.Fin.Properties using () renaming (_≟_ to _≟ᶠ_)
open import Data.Maybe using (just; nothing)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; subst; inspect; [_]) renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans)

open import RoutingLib.Algebra.FunctionProperties using (Selective; _×-Preserves_)
open import RoutingLib.Routing.Definitions
open import RoutingLib.Data.Graph using (Graph; _ᵉ∈ᵍ_; _ᵉ∈ᵍ?_)
open import RoutingLib.Data.Graph.EGPath using (EGPath; [_]; _∷_∣_∣_; source; destination)
open import RoutingLib.Data.Graph.EGPath.Properties

-----------
-- A module containing proofs about whether the a routing matrix's entries's paths line up with its position in the matrix
----------

module RoutingLib.Routing.AddingPaths.Consistent.PathAlignment
  {a b ℓ} (ra : RoutingAlgebra a b ℓ) 
  (⊕-sel : Selective (RoutingAlgebra._≈_ ra) (RoutingAlgebra._⊕_ ra))
  (one : (RoutingAlgebra.Route ra))
  {n : ℕ}
  (G : Graph (RoutingAlgebra.Step ra) n)
  where

  open RoutingAlgebra ra

  open import RoutingLib.Routing.AddingPaths.Consistent ra ⊕-sel one G
  open import RoutingLib.Routing.AddingPaths.Consistent.Properties ra ⊕-sel one G

  open import RoutingLib.Routing.Algorithms.DistributedBellmanFord crp 
  open import RoutingLib.Routing.Algorithms.DistributedBellmanFord.Properties crp using (σXᵢⱼ≈Aᵢₖ▷Xₖⱼ⊎Iᵢⱼ)

  PathAligned : RMatrix → Set (a ⊔ b ⊔ ℓ)
  PathAligned X = ∀ {i j x p x≈w[p]} → X i j ≈ᶜ croute x p x≈w[p] → source p ≡ i × destination p ≡ j

  DiagonalAligned : RMatrix → Set (a ⊔ b ⊔ ℓ)
  DiagonalAligned X = ∀ i → X i i ≈ᶜ croute one [ i ] refl

  abstract

    Iᶜ-pathAligned : PathAligned Iᶜ
    Iᶜ-pathAligned {i} {j} Iᵢⱼ≈xp with j ≟ᶠ i
    Iᶜ-pathAligned (crouteEq _ p≈[i]) | yes ≡-refl = p≈q⇨p₀≡q₀ (≈ₚ-sym p≈[i]) , p≈q⇨pₙ≡qₙ (≈ₚ-sym p≈[i])
    Iᶜ-pathAligned ()                 | no  _

    ⊕ₘ-pres-pathAlignment : _⊕ₘ_ ×-Preserves PathAligned
    ⊕ₘ-pres-pathAlignment {X} {Y} Xpa Ypa {i} {j} X⊕Yᵢⱼ≈xp with ⊕ᶜ-sel (X i j) (Y i j)
    ... | inj₁ X⊕Yᵢⱼ≈Xᵢⱼ = Xpa (≈ᶜ-trans (≈ᶜ-sym X⊕Yᵢⱼ≈Xᵢⱼ) X⊕Yᵢⱼ≈xp)
    ... | inj₂ X⊕Yᵢⱼ≈Yᵢⱼ = Ypa (≈ᶜ-trans (≈ᶜ-sym X⊕Yᵢⱼ≈Yᵢⱼ) X⊕Yᵢⱼ≈xp)

    σ-pres-pathAlignment : ∀ {X} → PathAligned X → PathAligned (σ X)
    σ-pres-pathAlignment {X} Xpa {i} {j} σXᵢⱼ≈xp with σXᵢⱼ≈Aᵢₖ▷Xₖⱼ⊎Iᵢⱼ ⊕ᶜ-sel X i j
    ... | inj₂ σXᵢⱼ≈Iᵢⱼ = Iᶜ-pathAligned (≈ᶜ-trans (≈ᶜ-sym σXᵢⱼ≈Iᵢⱼ) σXᵢⱼ≈xp)
    ... | inj₁ (k , σXᵢⱼ≈Aᵢₖ▷Xₖⱼ) with G i k | X k j | inspect (X k) j
    ...   | nothing | _     | _ = contradiction (≈ᶜ-trans (≈ᶜ-sym σXᵢⱼ≈Aᵢₖ▷Xₖⱼ) σXᵢⱼ≈xp) λ()
    ...   | just _  | cnull | _ = contradiction (≈ᶜ-trans (≈ᶜ-sym σXᵢⱼ≈Aᵢₖ▷Xₖⱼ) σXᵢⱼ≈xp) λ()
    ...   | just _  | croute y q y≈w[q] | [ Xₖⱼ≡yq ] with k ≟ᶠ source q | i ∉? q | (i , k) ᵉ∈ᵍ? G | Xpa (≈ᶜ-reflexive Xₖⱼ≡yq)
    ...     | no  _    | _        | _       | _          = contradiction (≈ᶜ-trans (≈ᶜ-sym σXᵢⱼ≈Aᵢₖ▷Xₖⱼ) σXᵢⱼ≈xp) λ()
    ...     | yes _    | no _     | _       | _          = contradiction (≈ᶜ-trans (≈ᶜ-sym σXᵢⱼ≈Aᵢₖ▷Xₖⱼ) σXᵢⱼ≈xp) λ()
    ...     | yes _    | yes  _   | no _    | _          = contradiction (≈ᶜ-trans (≈ᶜ-sym σXᵢⱼ≈Aᵢₖ▷Xₖⱼ) σXᵢⱼ≈xp) λ()
    ...     | yes k≡q₀ | yes  i∉q | yes e∈G | (_ , qₙ≡j) with ≈ᶜ-trans (≈ᶜ-sym σXᵢⱼ≈Aᵢₖ▷Xₖⱼ) σXᵢⱼ≈xp
    ...       | crouteEq v▷x≈y i∷q≈p = ≡-sym (p≈q⇨p₀≡q₀ {p = p} i∷q≈p) , ≡-trans (≡-sym (p≈q⇨pₙ≡qₙ {p = p} i∷q≈p)) qₙ≡j
      where 
      p : EGPath G
      p = i ∷ q ∣ i∉q ∣ subst (λ v → (i , v) ᵉ∈ᵍ G) k≡q₀ e∈G

    σ^-pres-pathAlignment : ∀ {X} → PathAligned X → ∀ t → PathAligned (σ^ t X)
    σ^-pres-pathAlignment Xpa zero    = Xpa
    σ^-pres-pathAlignment Xpa (suc t) = σ-pres-pathAlignment (σ^-pres-pathAlignment Xpa t)
