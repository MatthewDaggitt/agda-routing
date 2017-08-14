
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Fin.Properties using () renaming (_≟_ to _≟ᶠ_)
open import Data.Fin.Subset using (Subset; _∈_; ⁅_⁆)
open import Data.Fin.Dec using (_∈?_)
open import Data.Nat using (ℕ; zero; suc; z≤n; s≤s; _<_; _≤_; _+_; ≤-pred)
open import Data.Nat.Properties using (≤⇒pred≤; n≤m+n; <-trans)
open import Data.Nat.Properties.Simple using (+-suc)
open import Data.Vec using (Vec; _∷_; []; lookup; foldr; map; allFin)
open import Data.Maybe using (just; nothing)
open import Data.Product using (∃; ∃₂; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.List using (List; []; _∷_)
open import Level using (_⊔_)
open import Induction.WellFounded using (Acc; acc)
open import Relation.Binary.PropositionalEquality using (_≡_; subst; subst₂; cong; inspect; [_]; module ≡-Reasoning) renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans)
open import Relation.Nullary using (yes; no)
open import Function using (_∘_)
open import Algebra.FunctionProperties using (Selective)

open import RoutingLib.Asynchronous.Properties using ()
open import RoutingLib.Asynchronous.Snapshot using (Snapshot; snapshot)
open import RoutingLib.Asynchronous.Schedule
open import RoutingLib.Asynchronous.Schedule.Properties using (≈𝔸-refl)
open import RoutingLib.Asynchronous.Schedule.Times using (pseudoperiod𝔸)
open import RoutingLib.Asynchronous.Schedule.Times.Properties using (pseudoperiod𝔸-all; pseudoperiod𝔸-inc; previousActivation-all)
open import RoutingLib.Data.Graph using (Graph)
open import RoutingLib.Data.Graph.SimplePath using (SimplePath; []; [_]; _∷_; _∺_; _∷_∣_; _∺_∣_; length; source)
open import RoutingLib.Data.Graph.SimplePath.Properties using (length<n)
open import RoutingLib.Data.Nat.Properties using (≤-refl; m<n⇒n≡1+o; ≤-trans; <⇒≤)
open import RoutingLib.Routing.Definitions
open import RoutingLib.Induction.Nat using () renaming (<-well-founded to <-wf)

module RoutingLib.Routing.BellmanFord.AddingPaths
  {a b ℓ n-1} (𝓡𝓐 : RoutingAlgebra a b ℓ)
  (⊕-sel : Selective (RoutingAlgebra._≈_ 𝓡𝓐) (RoutingAlgebra._⊕_ 𝓡𝓐))
  (G : Graph (RoutingAlgebra.Step 𝓡𝓐) (suc n-1))
  where

  open import RoutingLib.Routing.AlgebraicPaths.Consistent 𝓡𝓐 ⊕-sel G using (𝓡𝓟ᶜ; CRoute; _⊕ᶜ_; _▷ᶜ_; weight; croute; cnull; ≈ᶜ-sym)
  open import RoutingLib.Routing.AlgebraicPaths.Inconsistent 𝓡𝓐 ⊕-sel G using (𝓡𝓟ⁱ; IRoute; iroute; inull; _≈ⁱ_; _⊕ⁱ_; _▷ⁱ_; ▷ⁱ-cong; ≈ⁱ-reflexive; ≈ⁱ-trans; ≈ⁱ-sym; size)
  open import RoutingLib.Routing.AlgebraicPaths.Inconsistent.Properties 𝓡𝓐 ⊕-sel G using (⊕ⁱ-sel; ▷ⁱ-size; size-cong)
  open import RoutingLib.Routing.AlgebraicPaths.Bisimilarity 𝓡𝓐 ⊕-sel G
  
  open RoutingAlgebra 𝓡𝓐
  open BisimilarityReasoning

  import RoutingLib.Routing.BellmanFord as BellmanFord
  import RoutingLib.Routing.BellmanFord.Properties as BellmanFordProperties
  module C  = BellmanFord 𝓡𝓟ᶜ
  module I  = BellmanFord 𝓡𝓟ⁱ
  module IP = BellmanFordProperties 𝓡𝓟ⁱ
{-
  private
    
    n : ℕ
    n = suc n-1

    n+2 : ℕ
    n+2 = suc (suc n)
      
    size<n : ∀ r → size r < n
    size<n inull        = s≤s z≤n
    size<n (iroute _ p) = length<n p


  _≃ₛ_ : ∀ {β₁ β₂ : 𝔹 n} {t₁ t₂ : 𝕋} → Snapshot (I.σ∥) β₁ t₁ → Snapshot (C.σ∥) β₂ t₂ → Set (a ⊔ b ⊔ ℓ)
  _≃ₛ_ {β₁} {β₂} {t₁} {t₂} s₁ s₂ = ∀ t i j k (βᵢⱼ≤t₁ : β₁ (t + t₁) i j ≤ t₁) (βᵢⱼ≤t₂ : β₂ (t + t₂) i j ≤ t₂) → s₁ i j (n≤m+n t t₁) βᵢⱼ≤t₁ k ≃ s₂ i j (n≤m+n t t₂) βᵢⱼ≤t₂ k



  abstract

    Iⁱ≃Iᶜ : I.I ≃ₘ C.I
    Iⁱ≃Iᶜ i j with j ≟ᶠ i
    ... | no  _ = nullEq
    ... | yes _ = routeEq refl []

{-
    δ'-≃ : ∀ {X Y} → X ≃ₘ Y → ∀ {t : ℕ} (acc : Acc _<_ t) → I.δ' acc X ≃ₘ C.δ' acc Y
    δ'-≃ X≃Y {zero}  (acc _) = X≃Y
    δ'-≃ X≃Y {suc t} (acc t-acc) i j with i ∈? α (suc t)
    ... | no  _ = δ'-≃ X≃Y (t-acc t ≤-refl) i j
    ... | yes _ = foldr-≃ (Iⁱ≃Iᶜ i j) {!!} --(map-≃ ? ? ?) -- (λ k → ▷-≃ i (lookup k (allFin n)) (δ'-≃ X≃Y (t-acc (β (suc t) i k) (causality t i k)) (lookup k (allFin n)) j)))
-}

    postulate δ-≃ : ∀ 𝕤 {X Y} → X ≃ₘ Y → ∀ t → I.δ 𝕤 t X ≃ₘ C.δ 𝕤 t Y


    --δ-≃ X≃Y t = δ'-≃ X≃Y (<-wf t)

    -- Flushing


    --open import RoutingLib.Asynchronous.Properties σ-parallelisation 𝕤

    open Schedule

