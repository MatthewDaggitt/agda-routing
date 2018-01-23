open import Data.Fin using (Fin) renaming (_≤_ to _≤F_)
open import Data.Fin.Subset using (Subset; ⊥; _∪_; ⁅_⁆) renaming (_⊆_ to _⊆ₛ_; _∈_ to _∈ₛ_; _∉_ to _∉ₛ_)
open import Data.Fin.Subset.Properties using (∉⊥; ⊥⊆; p⊆p∪q; q⊆p∪q; x∈⁅x⁆)
open import Data.Nat using (ℕ; zero; suc) renaming (_+_ to _+ℕ_; _<_ to _<ℕ_; _≤_ to _≤ℕ_; z≤n to z≤ℕn; s≤s to s≤ℕs)
open import Data.Nat.Properties using (1+n≰n) renaming (+-identityʳ to +-idʳℕ; +-suc to +ℕ-suc; ≤-reflexive to ≤ℕ-reflexive; ≤-trans to ≤ℕ-trans; n≤1+n to n≤ℕ1+n; ≤+≢⇒< to ≤+≢⇒ℕ<)
open import Data.Sum using (inj₁; inj₂; _⊎_)
open import Data.Product using (_×_; ∃; _,_; proj₁; proj₂; Σ)
open import Function using (_∘_)
open import Induction using (RecStruct)
open import Induction.Nat using (<-well-founded)
open import Induction.WellFounded using (Acc; acc; WfRec; Well-founded)
open import Level using () renaming (zero to lzero)
open import Relation.Binary using (Rel)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; _≢_; subst; sym; trans; cong)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Unary using (U; U-Universal)

open import RoutingLib.Asynchronous using (Parallelisation)
import RoutingLib.Asynchronous.Applications.AllPairs as AllPairs
open import RoutingLib.Asynchronous.Schedule using (Schedule; 𝕋)
open import RoutingLib.Data.NatInf
open import RoutingLib.Data.NatInf.Properties
open import RoutingLib.Data.Table using (Table; min∞; sum)
open import RoutingLib.Data.Table.All using (All)
open import RoutingLib.Data.Table.Any using (Any)
open import RoutingLib.Data.Table.Iterative using (k-min∞)
open import RoutingLib.Data.Table.Iterative.Membership.Properties
open import RoutingLib.Data.Table.Iterative.Properties
open import RoutingLib.Data.Table.Properties using (min∞[s]≤min∞[t]; min∞[t]≤x)

module RoutingLib.Asynchronous.Applications.AllPairs.Convergence {n}(𝕤 : Schedule n)(x₀ : AllPairs.Matrix n)(Cᵢ,ᵢ : ∀ i → x₀ i i ≡ N 0) where

  
  open AllPairs n hiding (f)
  open import RoutingLib.Asynchronous.Applications.AllPairs.Properties n
  open Schedule 𝕤
  open Parallelisation all-pairs-parallelisation
  open import RoutingLib.Asynchronous.Propositions.UresinDubois3 all-pairs-parallelisation
  open import RoutingLib.Asynchronous.Theorems.UresinDubois1 𝕤 all-pairs-parallelisation
  
  D₀ : Pred lzero
  D₀ i = U

  x₀∈D₀ : x₀ ∈ D₀
  x₀∈D₀ i = U-Universal (x₀ i)

  D₀-subst : ∀ {x y} → x ≈ y → x ∈ D₀ → y ∈ D₀
  D₀-subst {_} {y} _ _ i = U-Universal (y i)

  closed : ∀ x → x ∈ D₀ → f x ∈ D₀
  closed x _ i = U-Universal (f x i)

  f-monotone : ∀ {x y} → x ∈ D₀ × y ∈ D₀ → (∀ i → x i ≼ y i) → ∀ i → f x i ≼ f y i
  f-monotone {x} {y} ∈D x≼y i j = min∞[s]≤min∞[t] (x i j) (inj₁ (x≼y i j)) ≤-path-cost
      where
      ≤-path-cost : ∀ k → x i j ≤ path-cost y i j k ⊎
                           Σ (Fin n) (λ v → path-cost x i j v ≤ path-cost y i j k)
      ≤-path-cost k = inj₂ (k , path-cost-monotone x≼y i j k)

  iter-dec : ∀ K → iter x₀ (suc K) ≼ₘ iter x₀ K
  iter-dec zero i j = min∞[t]≤x (x₀ i j) (path-cost x₀ i j) (inj₁ ≤-refl)
  iter-dec (suc K) i = f-monotone
           ((λ l → U-Universal (iter x₀ (suc K))) , λ l → U-Universal (iter x₀ K))
           (λ j → iter-dec K j) i

  iter-fixed : ∀ t → iter x₀ (suc t) ≡ₘ iter x₀ t → ∀ K → iter x₀ t ≡ₘ iter x₀ (t +ℕ K)
  iter-fixed t iter≡ zero i j = cong (λ x → iter x₀ x i j) (sym (+-idʳℕ t))
  iter-fixed t iter≡ (suc K) i j = trans (sym (iter≡ i j)) (subst (iter x₀ (suc t) i j ≡_)
             (cong (λ x → iter x₀ x i j) (sym (+ℕ-suc t K)))
             (iter-fixed (suc t) (f-cong iter≡) K i j)) 

  changed : ∀ K i j → ℕ
  changed K i j with iter x₀ K i j ≟ iter x₀ (suc K) i j
  ... | yes _ = 1
  ... | no  _ with iter x₀ K i j
  ...   | ∞   = 1
  ...   | N n = 0

  distance : ℕ → ℕ
  distance K = sum {n} (λ i → sum {n} (λ j → changed K i j))

  X : ∀ K i {t} → t ≤ℕ K → iter x₀ K ≡ₘ iter x₀ (suc K) ⊎ (k-min∞ t ∞ (iter x₀ K i) ≡ ∞ ⊎ ∃ λ j → changed K i j ≡ 0)
  X zero i {.0} z≤ℕn with k-min∞[t]∈t 0 ∞ (x₀ i)
  ... | inj₁ ≡∞ = inj₂ (inj₁ ≡∞)
  ... | inj₂ (j , p)  with x₀ ≟ₘ iter x₀ 1
  ...   | yes iter≡ = inj₁ iter≡
  ...   | no  iter≢ = {!!}
  X (suc K) i {t} t≤K = {!!}

  postulate distance-dec : ∀ K → distance (suc K) ≤ℕ distance K


  iter≢⇒dis≢ : ∀ K → iter x₀ (suc K) ≢ₘ iter x₀ K → distance (suc K) ≢ distance K
  iter≢⇒dis≢ K iter≢ with iter x₀ (suc K) ≟ₘ iter x₀ (suc (suc K))
  ... | yes iterS≡ = {!!}
  ... | no  iterS≢ = {!!}

  -- postulate Z : ∀ i t → (∀ j → iter x₀ t i j ≡ ∞) ⊎ (∃ λ j → ∀ k → k ≤F j → iter x₀ t i k ≡ iter x₀ (suc t) i k)
{-
  fixed-nodes : ℕ → Table (Subset n) n
  fixed-nodes zero i = ⊥
  fixed-nodes (suc K) i with k-min∞[t]∈t (suc K) ∞ (iter x₀ (suc K) i)
  ... | inj₁ k-min≡∞ = fixed-nodes K i
  ... | inj₂ (j , k-min≡iterᵢⱼ) = (fixed-nodes K i) ∪ ⁅ j ⁆

  fixed-nodes-inc : ∀ K i → fixed-nodes K i ⊆ₛ fixed-nodes (suc K) i
  fixed-nodes-inc zero i x∈fixed[0] = ⊥⊆ x∈fixed[0]
  fixed-nodes-inc (suc K) i x∈fixed[sK] with k-min∞[t]∈t (suc (suc K)) ∞ (iter x₀ (suc (suc K)) i)
  ... | inj₁ _ = x∈fixed[sK]
  ... | inj₂ (j , _) = p⊆p∪q ⁅ j ⁆ x∈fixed[sK]

  Q : ∀ K i {j} {k-min∞≡iterKᵢⱼ : k-min∞ (suc K) ∞ (iter x₀ (suc K) i) ≡ iter x₀ (suc K) i j} →
      k-min∞[t]∈t (suc K) ∞ (iter x₀ (suc K) i) ≡ inj₂ (j , k-min∞≡iterKᵢⱼ) →
      j ∉ₛ fixed-nodes K i
  Q zero i k-min∈t = ∉⊥
  Q (suc K) i k-min∈t with k-min∞[t]∈t (suc K) ∞ (iter x₀ (suc K) i)
  ... | inj₁ ≡∞ = {!!}
  ... | inj₂ (j₁ , x) with Q K i {j₁} {x} {!refl!}
  ...   | y = {!!}

  A : ∀ K i → k-min∞ K ∞ (iter x₀ K i) ≡ k-min∞ K ∞ (iter x₀ (suc K) i)
  A zero i = {!!}
  A (suc K) i = {!!}


  Y : ∀ K i → (k-min∞ (suc K) ∞ (iter x₀ (suc K) i) ≡ ∞) ⊎
                (∃ λ j → j ∈ₛ fixed-nodes (suc K) i × j ∉ₛ fixed-nodes K i)
  Y K i with k-min∞[t]∈t (suc K) ∞ (iter x₀ (suc K) i)
  ... | inj₁ k-min≡∞ = inj₁ k-min≡∞
  Y zero i | inj₂ (j , x) = inj₂ (j , q⊆p∪q ⊥ ⁅ j ⁆ (x∈⁅x⁆ j) , ∉⊥)
  Y (suc K) i | inj₂ (j , x) with Y K i
  ...   | inj₁ ≡∞ = inj₁ (trans {!c!} {!!})
  ...   | inj₂ (k , _) = inj₂ (j , q⊆p∪q (fixed-nodes (suc K) i) ⁅ j ⁆ (x∈⁅x⁆ j) , {!!})
-}

  iter≢⇒dis< : ∀ K → iter x₀ (suc K) ≢ₘ iter x₀ K → distance (suc K) <ℕ distance K
  iter≢⇒dis< K iter≢ = ≤+≢⇒ℕ< (distance-dec K) (iter≢⇒dis≢ K iter≢)
  
  iter-fixed-point : ∀ {t} → Acc _<ℕ_ (distance t) → ∃ λ T → ∀ K → iter x₀ T ≡ₘ iter x₀ (T +ℕ K)
  iter-fixed-point {t} (acc rs) with iter x₀ (suc t) ≟ₘ iter x₀ t
  ... | yes iter≡ = t , iter-fixed t iter≡
  ... | no  iter≢ = iter-fixed-point (rs (distance (suc t)) (iter≢⇒dis< t iter≢))

  iter-converge : ∃ λ T → ∀ t → iter x₀ T ≈ iter x₀ (T +ℕ t)
  iter-converge = iter-fixed-point (<-well-founded (distance 0))
                 
  open proof x₀ D₀ x₀∈D₀ D₀-subst _≼_ ≼-refl ≼-reflexive ≼-antisym ≼-trans closed f-monotone iter-dec iter-converge hiding (ξ)

  open Theorem1 aco x₀∈D0

  converging-time : 𝕋
  converging-time = proj₁ theorem1

  converging-state : Matrix
  converging-state = ξ
