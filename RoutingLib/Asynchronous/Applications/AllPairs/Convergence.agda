open import Data.Fin using (Fin)
open import Data.Nat using (ℕ; zero; suc) renaming (_+_ to _+ℕ_; _<_ to _<ℕ_; _≤_ to _≤ℕ_)
open import Data.Nat.Properties using (1+n≰n) renaming (+-identityʳ to +-idʳℕ; +-suc to +ℕ-suc; ≤-reflexive to ≤ℕ-reflexive; ≤-trans to ≤ℕ-trans; n≤1+n to n≤ℕ1+n)
open import Data.Sum using (inj₁; inj₂; _⊎_)
open import Data.Product using (_×_; ∃; _,_; proj₁; proj₂; Σ)
open import Function using (_∘_)
open import Induction.Nat using (<-well-founded)
open import Induction.WellFounded using (Acc; acc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; trans; cong)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Unary using (U; U-Universal)

open import RoutingLib.Asynchronous using (Parallelisation)
import RoutingLib.Asynchronous.Applications.AllPairs as AllPairs
open import RoutingLib.Asynchronous.Schedule using (Schedule; 𝕋)
open import RoutingLib.Data.NatInf
open import RoutingLib.Data.NatInf.Properties
open import RoutingLib.Data.Table using (min∞)
open import RoutingLib.Data.Table.All using (All)
open import RoutingLib.Data.Table.Any using (Any)
open import RoutingLib.Data.Table.Properties using (min∞[s]≤min∞[t]; min∞[t]≤x)

module RoutingLib.Asynchronous.Applications.AllPairs.Convergence {n}(𝕤 : Schedule n)(x₀ : AllPairs.Matrix n)(Cᵢ,ᵢ : ∀ i → x₀ i i ≡ N 0) where

  
  open AllPairs n hiding (f)
  open import RoutingLib.Asynchronous.Applications.AllPairs.Properties n
  open Schedule 𝕤
  open Parallelisation all-pairs-parallelisation
  open import RoutingLib.Asynchronous.Propositions.UresinDubois3 all-pairs-parallelisation
  open import RoutingLib.Asynchronous.Theorems.UresinDubois1 𝕤 all-pairs-parallelisation
  
  D₀ : MPred
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

  postulate distance : ℕ → ℕ

  postulate iter≢⇒dis< : ∀ K → iter x₀ (suc K) ≢ₘ iter x₀ K → distance (suc K) <ℕ distance K

  iter-fixed-point : ∀ {t} → Acc _<ℕ_ (distance t) → ∃ λ T → ∀ K → iter x₀ T ≡ₘ iter x₀ (T +ℕ K)
  iter-fixed-point {t} (acc rs) with iter x₀ (suc t) ≟ₘ iter x₀ t
  ... | yes iter≡ = t , iter-fixed t iter≡
  ... | no  iter≢ = iter-fixed-point (rs (distance (suc t)) (iter≢⇒dis< t iter≢))

  iter-fixed-point-inc : ∀ {t} → (accₜ : Acc _<ℕ_ (distance t)) →
                           t ≤ℕ proj₁ (iter-fixed-point accₜ)
  iter-fixed-point-inc {t} (acc rs) with iter x₀ (suc t) ≟ₘ iter x₀ t
  ... | yes iter≡ = ≤ℕ-reflexive refl
  ... | no  iter≢ = ≤ℕ-trans (n≤ℕ1+n t) (iter-fixed-point-inc
                    (rs (distance (suc t)) (iter≢⇒dis< t iter≢)))

  iter-fixed-point-acc-irrelevant : ∀ {t} (a b : Acc _<ℕ_ (distance t)) →
                                 proj₁ (iter-fixed-point a) ≡ proj₁ (iter-fixed-point b)
  iter-fixed-point-acc-irrelevant {t} (acc a) (acc b) with iter x₀ (suc t) ≟ₘ iter x₀ t
  ... | yes iter≡ = refl
  ... | no  iter≢  = iter-fixed-point-acc-irrelevant
                       (a (distance (suc t)) (iter≢⇒dis< t iter≢))
                       (b (distance (suc t)) (iter≢⇒dis< t iter≢))
  
  iter-fixed-point-mono : ∀ {t} → (accₜ : Acc _<ℕ_ (distance t)) →
                       proj₁ (iter-fixed-point accₜ) ≤ℕ
                       proj₁ (iter-fixed-point (<-well-founded (distance (suc t))))
  iter-fixed-point-mono {t} (acc rs) with iter x₀ (suc t) ≟ₘ iter x₀ t
  ... | yes iter≡ = ≤ℕ-trans (n≤ℕ1+n t) (iter-fixed-point-inc (<-well-founded (distance (suc t))))
  ... | no  iter≢ = ≤ℕ-reflexive (iter-fixed-point-acc-irrelevant
                (rs (distance (suc t)) (iter≢⇒dis< t iter≢))
                (<-well-founded (distance (suc t))))

  iter-fixed-first : ∀ t → proj₁ (iter-fixed-point (<-well-founded (distance 0))) ≤ℕ
                            proj₁ (iter-fixed-point (<-well-founded (distance t)))
  iter-fixed-first zero = ≤ℕ-reflexive refl
  iter-fixed-first (suc t) = ≤ℕ-trans (iter-fixed-first t)
                     (iter-fixed-point-mono (<-well-founded (distance t)))

  iter≡⇒dis≡t : ∀ t → iter x₀ (suc t) ≡ₘ iter x₀ t →
                   proj₁ (iter-fixed-point (<-well-founded (distance t))) ≡ t
  iter≡⇒dis≡t t iter≡ with iter x₀ (suc t) ≟ₘ iter x₀ t
  ... | yes _    = refl
  ... | no iter≢ = contradiction iter≡ iter≢

  t<T⇒iter≢ : ∀ {t} → t <ℕ proj₁ (iter-fixed-point (<-well-founded (distance 0))) →
               iter x₀ t ≢ₘ iter x₀ (suc t)
  t<T⇒iter≢ {t} t<T with iter x₀ (suc t) ≟ₘ iter x₀ t
  ... | yes iter≡ = contradiction (≤ℕ-trans t<T
        (subst ((proj₁ (iter-fixed-point (<-well-founded (distance 0)))) ≤ℕ_)
        (iter≡⇒dis≡t t iter≡) (iter-fixed-first t))) 1+n≰n
  ... | no iter≢ = iter≢ ∘ symₘ

  iter-converge : ∃ λ T → (∀ t → iter x₀ T ≈ iter x₀ (T +ℕ t)) ×
                                (∀ {t} → t <ℕ T → iter x₀ t ≉ iter x₀ (suc t))
  iter-converge = proj₁ (iter-fixed-point (<-well-founded (distance 0))) ,
                  proj₂ (iter-fixed-point (<-well-founded (distance 0))) ,
                  t<T⇒iter≢

  open proof x₀ D₀ x₀∈D₀ D₀-subst _≼_ ≼-refl ≼-reflexive ≼-antisym ≼-trans closed f-monotone iter-dec iter-converge hiding (ξ)

  open Theorem1 aco x₀∈D0

  converging-time : 𝕋
  converging-time = proj₁ theorem1

  converging-state : Matrix
  converging-state = ξ
