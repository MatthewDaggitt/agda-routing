open import Data.List using (List; []; _∷_; map; concat)
open import Data.Nat using (ℕ; zero; suc; _<_; _≤_; _+_; _≤?_)
open import Data.Nat.Properties using (n≤m+n)
open import Data.Fin using (Fin)
open import Data.Product using (∃; _×_)
open import Relation.Binary.PropositionalEquality using (_≢_)
open import Relation.Nullary using (yes; no)

open import RoutingLib.Asynchronous
open import RoutingLib.Asynchronous.Schedule using (Schedule; 𝕋; 𝔹; Dynamic)
open import RoutingLib.Asynchronous.Schedule.Times using (expiryᵢⱼ)
open import RoutingLib.Data.List using (allFin)


module RoutingLib.Asynchronous.Snapshot {a ℓ n} (p : Parallelisation a ℓ n) where
  
    open Schedule
    open Parallelisation p

    -- Snapshot
    Snapshot : 𝔹 n → ℕ → Set a
    Snapshot β t = ∀ {t'} i j → t ≤ t' → β t' i j ≤ t → Mᵢ {j}

    snapshot : ∀ 𝕤 t → M → Snapshot (β 𝕤) t
    snapshot 𝕤 t X {t'} i j _ _ = δ 𝕤 (β 𝕤 t' i j) X j

    infix 4 _≈ₛ_
    _≈ₛ_ : ∀ {β₁ β₂ t₁ t₂} → Snapshot β₁ t₁ → Snapshot β₂ t₂ → Set ℓ
    _≈ₛ_ {β₁} {β₂} {t₁} {t₂} s₁ s₂ = ∀ t i j (βᵢⱼ≤t₁ : β₁ (t + t₁) i j ≤ t₁) (βᵢⱼ≤t₂ : β₂ (t + t₂) i j ≤ t₂) → s₁ i j (n≤m+n t t₁) βᵢⱼ≤t₁ ≈ᵢ s₂ i j (n≤m+n t t₂) βᵢⱼ≤t₂




    -----------
    -- Lists --
    -----------

    toListᵢⱼ-bounded : ∀ {β tₛ} → Snapshot β tₛ → (t : 𝕋) → ∀ (i j : Fin n) → List (Mᵢ {j})
    toListᵢⱼ-bounded {β} {tₛ} snapshot zero    i j = []
    toListᵢⱼ-bounded {β} {tₛ} snapshot (suc t) i j with tₛ ≤? suc t | β (suc t) i j ≤? tₛ
    ... | no _     | _       = toListᵢⱼ-bounded snapshot t i j
    ... | _        | no  _   = toListᵢⱼ-bounded snapshot t i j
    ... | yes tₛ≤t | yes β≤tₛ = snapshot i j tₛ≤t β≤tₛ ∷ toListᵢⱼ-bounded snapshot t i j

    toListᵢⱼ : ∀ {β tₛ} → Dynamic β → Snapshot β tₛ → ∀ (i j : Fin n) → List (Mᵢ {j})
    toListᵢⱼ {β} {tₛ} dynamic snapshot i j = toListᵢⱼ-bounded snapshot (expiryᵢⱼ dynamic tₛ i j) i j

    toListⱼ : ∀ {β tₛ} → Dynamic β → Snapshot β tₛ → ∀ (j : Fin n) → List (Mᵢ {j})
    toListⱼ dynamic snapshot j = concat (map (λ i → toListᵢⱼ dynamic snapshot i j) (allFin n))
