open import Function.Bijection using (Bijection)
open import Level using (Level; _⊔_) renaming (suc to lsuc)
open import Relation.Binary using (REL)

open import RoutingLib.Routing.Algebra
open import RoutingLib.Routing.BellmanFord

module RoutingLib.Routing.Algebra.Bisimulation where


  record Bisimilar {a₁ b₁ ℓ₁ a₂ b₂ ℓ₂ n} (ℓ₃ ℓ₄ : Level)
                   (𝓐 : RawRoutingAlgebra a₁ b₁ ℓ₁)
                   (𝓑 : RawRoutingAlgebra a₂ b₂ ℓ₂)
                   : Set (lsuc (a₁ ⊔ a₂ ⊔ b₁ ⊔ b₂ ⊔ ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄))where
    constructor bisimilar

    module A = RawRoutingAlgebra 𝓐
    module B = RawRoutingAlgebra 𝓑

    infix 4 _~ᵣ_ _~ₛ_

    field
      _~ᵣ_ : REL A.Route B.Route ℓ₃

      σ-cong : ∀ {X Y} → (∀ i j → X i j ~ᵣ Y i j) → σ 𝓐 ? X ~ᵣ σ 𝓑 ? Y
