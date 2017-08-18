open import Data.Nat using (ℕ; _≤_; _≤?_; _<_; _+_; _∸_; zero; suc; z≤n; s≤s; _≟_; ≤-pred)
open import Data.Nat.Properties using (n≤1+n; ≰⇒>; +-∸-assoc; n∸n≡0; ≤-refl; ≤-antisym; ≤+≢⇒<; ≤-reflexive; ≤-trans; +-assoc; +-identityʳ; _<?_; ≮⇒≥; <⇒≤; +-cancelʳ-≡)
open import Data.Fin using (Fin)
open import Data.Fin.Subset using (_∈_; ⊤)
open import Data.Fin.Subset.Properties using (∈⊤)
open import Data.Fin.Dec using (_∈?_; all?; ¬∀⟶∃¬)
open import Data.Product using (∃; _,_; _×_)
open import Relation.Binary using (_Preserves_⟶_; _⇒_; Reflexive; Symmetric; Transitive; Decidable; IsEquivalence; Setoid)
open import Relation.Binary.PropositionalEquality using (_≡_; cong; refl; sym; trans; _≗_; subst; module ≡-Reasoning)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Induction.WellFounded using (Acc; acc)
open import Induction.Nat using () renaming (<-well-founded to <-wf)

open import RoutingLib.Asynchronous
open import RoutingLib.Asynchronous.Schedule using (Schedule; 𝕤-sync; _⟦_⟧≈⟦_⟧_)
open import RoutingLib.Asynchronous.Schedule.Properties using (⟦⟧≈⟦⟧-fastForward)
open import RoutingLib.Data.Nat.Properties using (m≤n⇒m∸n≡0; m>n⇒m∸n≢0; w∸x≡y∸z⇒v+x≡w∧v+y≡z)
open import RoutingLib.Data.Table.Relation.Equality as TableEquality

module RoutingLib.Asynchronous.Properties {a ℓ n} {S : Setoid a ℓ} (p : Parallelisation S n) where
  
  open Parallelisation p

  -------------------------
  -- Equality properties --
  -------------------------

  open TableEquality S public using () renaming
    ( ≈ₜ-reflexive to ≈ₘ-reflexive
    ; ≈ₜ-refl to ≈ₘ-refl
    ; ≈ₜ-sym to ≈ₘ-sym
    ; ≈ₜ-trans to ≈ₘ-trans
    ; ≈ₜ-isEquivalence to ≈ₘ-isEquivalence
    ; 𝕋ₛ to Sₘ
    )
    
  -- Equality
  
  ≈ₘ-dec : Decidable _≈ᵢ_ → Decidable (_≈ₘ_ {n})
  ≈ₘ-dec _≟ᵢ_ X Y = all? (λ i → (X i) ≟ᵢ (Y i))

  ≉ₘ-witness : Decidable _≈ᵢ_ → ∀ {X Y} → X ≉ₘ Y → ∃ λ i → ¬ (X i ≈ᵢ Y i)
  ≉ₘ-witness _≟ᵢ_ {X} {Y} X≉Y with all? (λ i → X i ≟ᵢ Y i)
  ... | yes all  = contradiction all X≉Y
  ... | no  ¬all = ¬∀⟶∃¬ n (λ i → X i ≈ᵢ Y i) (λ i → X i ≟ᵢ Y i) ¬all
  

  ----------------------
  -- State properties --
  ----------------------

  open Schedule

  module _ (σ-cong : σ Preserves _≈ₘ_ ⟶ _≈ₘ_) where
    
    abstract

      -------------------
      -- δ' properties --
      -------------------

      -- Congruence properties
      δ'-stateCong : ∀ 𝕤 {X Y} → X ≈ₘ Y → ∀ {t} (tAcc : Acc _<_ t) → δ' 𝕤 tAcc X ≈ₘ δ' 𝕤 tAcc Y
      δ'-stateCong 𝕤 X≈Y {zero}  _ = X≈Y
      δ'-stateCong 𝕤 X≈Y {suc t} (acc 1+tAcc) i with i ∈? α 𝕤 (suc t)
      ... | yes _ = σ-cong (λ k → δ'-stateCong 𝕤 X≈Y (1+tAcc _ (causal 𝕤 t i k)) k) i
      ... | no  _ = δ'-stateCong 𝕤 X≈Y (1+tAcc t ≤-refl) i
  
      δ'-timeCong : ∀ 𝕤 X {s t} → s ≡ t → (tAcc : Acc _<_ t) (sAcc : Acc _<_ s) → δ' 𝕤 tAcc X ≈ₘ δ' 𝕤 sAcc X
      δ'-timeCong 𝕤 X {zero}  refl _          _          = ≈ₘ-refl
      δ'-timeCong 𝕤 X {suc t} refl (acc tAcc) (acc sAcc) i with i ∈? α 𝕤 (suc t)
      ... | yes _ = σ-cong (λ k → δ'-timeCong 𝕤 X refl (tAcc _ (causal 𝕤 t i k)) (sAcc _ (causal 𝕤 t i k)) k) i
      ... | no  _ = δ'-timeCong 𝕤 X refl (tAcc t ≤-refl) (sAcc t ≤-refl) i

      -- Activation properties
      δ'-unactivated : ∀ 𝕤 X {t} (tAcc : Acc _<_ t) i {p} (pAcc : Acc _<_ p) → p ≤ t → (∀ {t'} → t' ≤ t → i ∈ α 𝕤 t' → t' ≤ p) → δ' 𝕤 tAcc X i ≈ᵢ δ' 𝕤 pAcc X i
      δ'-unactivated 𝕤 X {zero}  _          i {_} pAcc z≤n p-latest = ≈ᵢ-refl
      δ'-unactivated 𝕤 X {suc t} (acc tAcc) i {p} pAcc p≤t+1 p-latest with p ≟ suc t 
      ... | yes p≡t+1 = δ'-timeCong 𝕤 X p≡t+1 (acc tAcc) _ i
      ... | no  p≢t+1 with i ∈? α 𝕤 (suc t) 
      ... | no  _     = δ'-unactivated 𝕤 X (tAcc t ≤-refl) i pAcc (≤-pred (≤+≢⇒< p≤t+1 p≢t+1)) (λ t'≤t → p-latest (≤-trans t'≤t (n≤1+n _)))
      ... | yes i∈αₜ₊₁ = contradiction (p-latest ≤-refl i∈αₜ₊₁) (λ t+1≤p → p≢t+1 (≤-antisym p≤t+1 t+1≤p))

      δ'-activated : ∀ 𝕤 X {t} (tAcc : Acc _<_ (suc t)) {i} → i ∈ α 𝕤 (suc t) → δ' 𝕤 tAcc X i ≈ᵢ σ (λ k → δ 𝕤 (β 𝕤 (suc t) i k) X k) i
      δ'-activated 𝕤 X {t} (acc 1+tAcc) {i} i∈α₁₊ₜ with i ∈? α 𝕤 (suc t)
      ... | no i∉α₁₊ₜ = contradiction i∈α₁₊ₜ i∉α₁₊ₜ
      ... | yes _    = σ-cong (λ k → δ'-timeCong 𝕤 X {s = β 𝕤 (suc t) i k} {β 𝕤 (suc t) i k} refl _ _ k) i

      ------------------
      -- δ properties --
      ------------------

      -- Activation properties
      δ-unactivated : ∀ 𝕤 {t p} X i → p ≤ t → (∀ {t'} → t' ≤ t → i ∈ α 𝕤 t' → t' ≤ p) → δ 𝕤 t X i ≈ᵢ δ 𝕤 p X i
      δ-unactivated 𝕤 {t} {p} X i = δ'-unactivated 𝕤 X (<-wf t) i (<-wf p)
    
      δ-activated : ∀ 𝕤 X t {i} → i ∈ α 𝕤 (suc t) → δ 𝕤 (suc t) X i ≈ᵢ σ (λ k → δ 𝕤 (β 𝕤 (suc t) i k) X k) i
      δ-activated 𝕤 X t = δ'-activated 𝕤 X (<-wf (suc t))


      ---------------
      -- Snapshots --
      ---------------

      open import RoutingLib.Asynchronous.Snapshot p

      ≈ₛ⇒≈ₘ' : ∀ {𝕤₁ 𝕤₂ t₁ t₂} X₁ X₂ → 𝕤₁ ⟦ t₁ ⟧≈⟦ t₂ ⟧ 𝕤₂ → snapshot 𝕤₁ t₁ X₁ ≈ₛ snapshot 𝕤₂ t₂ X₂ → 
                δ 𝕤₁ t₁ X₁ ≈ₘ δ 𝕤₂ t₂ X₂ → ∀ t (t+t₁Acc : Acc _<_ (t + t₁)) (t+t₂Acc : Acc _<_ (t + t₂)) → δ' 𝕤₁ t+t₁Acc X₁ ≈ₘ δ' 𝕤₂ t+t₂Acc X₂
      ≈ₛ⇒≈ₘ' {𝕤₁} {𝕤₂} {t₁} {t₂} X₁ X₂ (α-eq , β-eq) snapshot-eq δᵗ¹X₁≈δᵗ²X₂ zero   t₁Acc t₂Acc = ≈ₘ-trans (≈ₘ-trans (δ'-timeCong 𝕤₁ X₁ refl t₁Acc (<-wf t₁)) δᵗ¹X₁≈δᵗ²X₂) (δ'-timeCong 𝕤₂ X₂ refl (<-wf t₂) t₂Acc)
      ≈ₛ⇒≈ₘ' {𝕤₁} {𝕤₂} {t₁} {t₂} X₁ X₂ (α-eq , β-eq) snapshot-eq δᵗ¹X₁≈δᵗ²X₂ (suc t) (acc t+t₁Acc) (acc t+t₂Acc) i with i ∈? α 𝕤₁ (suc (t + t₁)) | i ∈? α 𝕤₂ (suc (t + t₂))
      ... | no  _   | no _    = ≈ₛ⇒≈ₘ' X₁ X₂ (α-eq , β-eq) snapshot-eq δᵗ¹X₁≈δᵗ²X₂ t (t+t₁Acc (t + t₁) ≤-refl) (t+t₂Acc (t + t₂) ≤-refl) i
      ... | yes i∈α | no  i∉α = contradiction (subst (i ∈_) (     α-eq t)  i∈α) i∉α
      ... | no  i∉α | yes i∈α = contradiction (subst (i ∈_) (sym (α-eq t)) i∈α) i∉α
      ... | yes _   | yes _   = σ-cong result i
        where
        result : ∀ k → δ' 𝕤₁ (t+t₁Acc (β 𝕤₁ (suc t + t₁) i k) _) X₁ k ≈ᵢ δ' 𝕤₂ (t+t₂Acc (β 𝕤₂ (suc t + t₂) i k) _) X₂ k
        result k with t₁ <? β 𝕤₁ (suc (t + t₁)) i k | t₂ <? β 𝕤₂ (suc (t + t₂)) i k
        ... | no  t₁≮β | no  t₂≮β = ≈ᵢ-trans (≈ᵢ-trans (δ'-timeCong 𝕤₁ X₁ {β 𝕤₁ (suc t + t₁) i k} refl _ _ k) (snapshot-eq t i k (≮⇒≥ t₁≮β) (≮⇒≥ t₂≮β))) (δ'-timeCong 𝕤₂ X₂ {β 𝕤₂ (suc t + t₂) i k} refl _ _ k)
        ... | no  t₁≮β | yes t₂<β = contradiction (trans (sym (β-eq t i k)) (m≤n⇒m∸n≡0 (≮⇒≥ t₁≮β))) (m>n⇒m∸n≢0 t₂<β)
        ... | yes t₁<β | no  t₂≮β = contradiction (trans      (β-eq t i k)  (m≤n⇒m∸n≡0 (≮⇒≥ t₂≮β))) (m>n⇒m∸n≢0 t₁<β)
        ... | yes t₁<β | yes t₂<β with w∸x≡y∸z⇒v+x≡w∧v+y≡z (β-eq t i k) (<⇒≤ t₁<β) (<⇒≤ t₂<β)
        ... | (o , o+t₁≡β , o+t₂≡β) = ≈ᵢ-trans (≈ᵢ-trans (δ'-timeCong 𝕤₁ X₁ o+t₁≡β _ _ k) (≈ₛ⇒≈ₘ' X₁ X₂ (α-eq , β-eq) snapshot-eq δᵗ¹X₁≈δᵗ²X₂ o (t+t₁Acc (o + t₁) (s≤s (≤-trans (≤-reflexive o+t₁≡β) (≤-pred (causal 𝕤₁ (t + t₁) i k))))) (<-wf (o + t₂)) k)) (δ'-timeCong 𝕤₂ X₂ (sym o+t₂≡β) _ _ k)


      ≈ₛ⇒≈ₘ : ∀ {𝕤₁ 𝕤₂ t₁ t₂} X₁ X₂ → 𝕤₁ ⟦ t₁ ⟧≈⟦ t₂ ⟧ 𝕤₂ → snapshot 𝕤₁ t₁ X₁ ≈ₛ snapshot 𝕤₂ t₂ X₂ → 
                δ 𝕤₁ t₁ X₁ ≈ₘ δ 𝕤₂ t₂ X₂ → ∀ t → δ 𝕤₁ (t + t₁) X₁ ≈ₘ δ 𝕤₂ (t + t₂) X₂
      ≈ₛ⇒≈ₘ X₁ X₂ 𝕤-eq snapshot-eq δX₁≈δX₂ t = ≈ₛ⇒≈ₘ' X₁ X₂ 𝕤-eq snapshot-eq δX₁≈δX₂ t (<-wf _) (<-wf _)

      
