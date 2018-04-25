open import Data.List using (List; length; []; _∷_; filter)
open import Data.List.Any using (Any; here; there)
import Data.List.Any.Membership as Memb
open import RoutingLib.Data.List.Membership.Setoid.Properties using (∈-filter⁻; ∈-filter⁺; ∈-resp-≈)
open import Data.List.Properties using (length-filter; filter-some)
open import Data.Nat using (ℕ; zero; suc; _+_; _<_; _≤_; z≤n; s≤s) renaming (_≟_ to _≟ℕ_)
open import Data.Nat.Properties using (+-suc; +-identityʳ; ≤-trans; ≤-step; m≤m+n; ≤-reflexive; pred-mono; ≤+≢⇒<; ≤-refl; <⇒≤)
open import Data.Product using (_×_; ∃; proj₁; proj₂; _,_)
open import Function using (_∘_)
open import Relation.Binary using (Setoid; Rel; Reflexive; Antisymmetric; Transitive; _⇒_; Decidable)
open import Relation.Binary.PropositionalEquality using (subst; cong; _≡_; trans; sym; refl)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Induction.Nat using (<-well-founded)
open import Induction.WellFounded using (Acc; acc)

open import RoutingLib.Asynchronous using (Parallelisation)
-- open import RoutingLib.Data.List using (dfilter)
-- open import RoutingLib.Data.List.Properties using (|dfilter[xs]|<|xs|)
open import RoutingLib.Data.Table using (Table)
open import RoutingLib.Relation.Unary.Consequences using (P?⇒¬P?)


module RoutingLib.Asynchronous.Propositions.UresinDubois4 {a ℓ n}
                                                          {S : Table (Setoid a ℓ) n}
                                                          (𝕡 : Parallelisation S)
  where

  open Parallelisation 𝕡 using (f)
  open import RoutingLib.Asynchronous.Propositions.UresinDubois3 𝕡 using () renaming (module Proof to Prop3-proof)
  open import RoutingLib.Asynchronous.Theorems.Core 𝕡 using (ACO; Start; SynchronousConditions; FiniteConditions; iter)
  open import RoutingLib.Data.Table.IndexedTypes S
  open Memb M-setoid using () renaming (_∈_ to _∈L_; _⊆_ to _⊆L_)

  module Proof {p} (finiteCond : FiniteConditions p) where

    open FiniteConditions finiteCond
    open Start start
    open M-poset poset hiding (trans)

    closed-trans : ∀ K → iter x₀ K ∈ D₀
    closed-trans zero    i = x₀∈D₀ i
    closed-trans (suc K) i = D₀-closed (iter x₀ K) (closed-trans K) i

    iter-decreasing : ∀ K → iter x₀ (suc K) ≼ iter x₀ K
    iter-decreasing K i = f-nonexpansive (closed-trans K) i

    iter-decreasing-full : ∀ {k t} → k ≤ t → iter x₀ t ≼ iter x₀ k
    iter-decreasing-full {.0} {zero} z≤n = ≼-refl
    iter-decreasing-full {k} {suc t} k≤t with k ≟ℕ suc t
    ... | yes refl = ≼-refl
    ... | no  k≢st = ≼-trans (iter-decreasing t) (iter-decreasing-full {k} {t} (pred-mono (≤+≢⇒< k≤t k≢st)))

    D₀-list : List M
    D₀-list = proj₁ D₀-finite

    x∈D₀⇒x∈D₀-list : ∀ {x} → x ∈ D₀ → x ∈L D₀-list
    x∈D₀⇒x∈D₀-list = proj₂ D₀-finite

    D₀-fixed : ℕ → List M
    D₀-fixed zero = D₀-list
    D₀-fixed (suc K) = filter (P?⇒¬P? (iter x₀ K ≟_)) (D₀-fixed K)

    iterK∈D₀-list : ∀ K → iter x₀ K ∈L D₀-list
    iterK∈D₀-list K = x∈D₀⇒x∈D₀-list (closed-trans K)

    D₀-fixed-decreasing : ∀ K → D₀-fixed (suc K) ⊆L  D₀-fixed K
    D₀-fixed-decreasing K x∈DsK = proj₁ (∈-filter⁻ M-setoid
             ((P?⇒¬P? (iter x₀ K ≟_)))
             ((λ x≈y x≉iterK → x≉iterK ∘ λ iterK≈y → ≈-trans iterK≈y (≈-sym x≈y)))
             x∈DsK)

    iter-fixed : ∀ K → iter x₀ K ≈ iter x₀ (suc K) → ∀ t → iter x₀ K ≈ iter x₀ (K + t)
    iter-fixed K iter≈ zero = ≈-cong (iter x₀) (sym (+-identityʳ K))
    iter-fixed K iter≈ (suc t) = ≈-trans iter≈ (subst (iter x₀ (suc K) ≈_)
               (cong (λ x → λ i → iter x₀ x i) (sym (+-suc K t)))
               (iter-fixed (suc K) (f-cong iter≈) t))


    x≼y≼z∧x≉y⇒x≉z : ∀ {x y z} → x ≼ y → y ≼ z → x ≉ y → x ≉ z
    x≼y≼z∧x≉y⇒x≉z x≼y y≼z x≉y x≈z = contradiction
          (≼-antisym x≼y (≼-trans y≼z (≼-reflexive (≈-sym x≈z))))
          x≉y

    iterK∈D₀-fixedt : ∀ K → iter x₀ K ≉ iter x₀ (suc K) → ∀ {t} → t ≤ K →
                      iter x₀ (suc K) ∈L D₀-fixed t
    iterK∈D₀-fixedt K iter≉ {zero} t≤K = iterK∈D₀-list (suc K)
    iterK∈D₀-fixedt K iter≉ {suc t} t≤K = ∈-filter⁺ M-setoid (P?⇒¬P? (iter x₀ t ≟_))
              (λ x≈y x≉iterK → x≉iterK ∘ λ iterK≈y → ≈-trans iterK≈y (≈-sym x≈y))
              ((x≼y≼z∧x≉y⇒x≉z (iter-decreasing K)
                (iter-decreasing-full (<⇒≤ t≤K)) (iter≉ ∘ ≈-sym)) ∘ ≈-sym)
              (iterK∈D₀-fixedt K iter≉ (<⇒≤ t≤K))

    iter≉⇒iter∈D₀-fixed : ∀ K → iter x₀ K ≉ iter x₀ (suc K) → iter x₀ K ∈L D₀-fixed K
    iter≉⇒iter∈D₀-fixed zero _ = iterK∈D₀-list zero
    iter≉⇒iter∈D₀-fixed (suc K) iter≉ = ∈-filter⁺ M-setoid (P?⇒¬P? (iter x₀ K ≟_))
                    (λ x≈y x≉iterK → x≉iterK ∘ λ iterK≈y → ≈-trans iterK≈y (≈-sym x≈y))
                    {iter x₀ (suc K)}
                    (λ iter≈ → contradiction (≈-trans (≈-sym iter≈)
                       (subst (iter x₀ K ≈_)
                         (cong (iter x₀) (trans (+-suc K 1)
                           (cong suc (trans (+-suc K 0)
                             (cong suc (+-identityʳ K))))))
                         (iter-fixed K iter≈ 2)))
                       iter≉)
                    {D₀-fixed K}
                    (iterK∈D₀-fixedt K (λ iter≈ → contradiction (f-cong iter≈) iter≉) ≤-refl)


    y∈xs⇒¬¬y∈xs : ∀ (xs : List M) y → y ∈L xs → Any (λ x → ¬ (λ z → y ≉ z) x) xs
    y∈xs⇒¬¬y∈xs [] y ()
    y∈xs⇒¬¬y∈xs (x ∷ xs) y (here px) = here λ y≉x → contradiction px y≉x
    y∈xs⇒¬¬y∈xs (x ∷ xs) y (there y∈xs) = there (y∈xs⇒¬¬y∈xs xs y y∈xs)

    D₀-fixed-length-dec : ∀ K  → iter x₀ K ≉ iter x₀ (suc K) →
                          length (D₀-fixed (suc K)) < length (D₀-fixed K)
    D₀-fixed-length-dec K iter≉ = filter-some (P?⇒¬P? (iter x₀ K ≟_)) (D₀-fixed K)
      (y∈xs⇒¬¬y∈xs (D₀-fixed K) (iter x₀ K) (iter≉⇒iter∈D₀-fixed K iter≉))

    iter-fixed-point : ∀ {K} → Acc _<_ (length (D₀-fixed K)) →
                                 ∃ λ T → ∀ t → iter x₀ T ≈ iter x₀ (T + t)
    iter-fixed-point {K} (acc rs) with iter x₀ K ≟ iter x₀ (suc K)
    ... | yes iter≈ = K , iter-fixed K iter≈
    ... | no  iter≉ = iter-fixed-point {suc K}
                      (rs (length (D₀-fixed (suc K))) (D₀-fixed-length-dec K iter≉))

    iter-converge : ∃ λ T → ∀ t → iter x₀ T ≈ iter x₀ (T + t)
    iter-converge = iter-fixed-point {0} (<-well-founded (length (D₀-list)))

    syncCond : SynchronousConditions p
    syncCond = record {
      start           = start ;
      poset           = poset ;
      f-monotone      = f-monotone ;
      iter-decreasing = iter-decreasing ;
      iter-converge   = iter-converge 
      }

    open Prop3-proof syncCond using () renaming (aco to Prop3-aco)

    aco : ACO p
    aco = Prop3-aco
