open import Data.Fin using (Fin) renaming (_≤_ to _≤F_)
open import Data.List using (List; []; _∷_; length)
open import Data.List.All using (All) renaming ([] to [A]; _∷_ to _∷A_; tabulate to tabulateAll)
open import Data.List.Any using (Any; here; there)
import Data.List.Any.Membership as Memb
import Data.List.Any.Membership.Properties as MembProp
open import Data.Nat using (ℕ; zero; suc; _∸_) renaming (_+_ to _+ℕ_; _<_ to _<ℕ_; _≤_ to _≤ℕ_; z≤n to z≤ℕn; s≤s to s≤ℕs; _≟_ to _≟ℕ_)
open import Data.Nat.Properties using (1+n≰n; +-monoʳ-<; m+n∸m≡n) renaming (+-identityʳ to +-idʳℕ; +-suc to +ℕ-suc; ≤-reflexive to ≤ℕ-reflexive; ≤-trans to ≤ℕ-trans; n≤1+n to n≤ℕ1+n; ≤+≢⇒< to ≤+≢⇒ℕ<; ≤-refl to ≤ℕ-refl; n≤m+n to n≤ℕm+n; m≤m+n to m≤ℕm+n; <⇒≤ to <ℕ⇒≤ℕ; ≤-step to ≤ℕ-step)
open import Data.Sum using (inj₁; inj₂; _⊎_)
open import Data.Product using (_×_; ∃; _,_; proj₁; proj₂; Σ)
open import Function using (_∘_; id)
open import Induction using (RecStruct)
open import Induction.Nat using (<-well-founded)
open import Induction.WellFounded using (Acc; acc; WfRec; Well-founded)
open import Level using () renaming (zero to lzero)
open import Relation.Binary using (Rel; Setoid; Preorder)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; _≢_; subst; sym; trans; cong; subst₂; setoid)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Unary using (U; U-Universal; Decidable)

open import RoutingLib.Asynchronous using (Parallelisation)
import RoutingLib.Asynchronous.Applications.AllPairs as AllPairs
open import RoutingLib.Asynchronous.Schedule using (Schedule; 𝕋)
open import RoutingLib.Data.List using (allFinPairs; dfilter)
open import RoutingLib.Data.List.Membership.Propositional.Properties using (∈-dfilter⁺; ∈-combine⁺; ∈-tabulate⁺; ∈-dfilter⁻; ∈-allFinPairs⁺)
open import RoutingLib.Data.List.Properties using (|dfilter[xs]|≡|xs|⇒dfilter[xs]≡xs; dfilter[xs]≡xs; |dfilter[xs]|≤|xs|)
open import RoutingLib.Data.NatInf
open import RoutingLib.Data.NatInf.Properties
open import RoutingLib.Data.Table using (Table; min∞; sum; max)
open import RoutingLib.Data.Table.Any using (Any)
open import RoutingLib.Data.Table.Properties using (min∞[s]≤min∞[t]; min∞[t]≤x; t≤max[t]; sum[s]≤sum[t]; sum[s]<sum[t])
open import RoutingLib.Data.Table.Membership.Propositional.Properties using (min∞[t]∈t)

module RoutingLib.Asynchronous.Applications.AllPairs.Convergence {n}(𝕤 : Schedule n)(x₀ : AllPairs.Matrix n)(Cᵢ,ᵢ : ∀ i → x₀ i i ≡ N 0) where

  
  open AllPairs n hiding (f)
  open import RoutingLib.Asynchronous.Applications.AllPairs.Properties n
  open Schedule 𝕤
  open Parallelisation all-pairs-parallelisation
  open import RoutingLib.Asynchronous.Propositions.UresinDubois3 all-pairs-parallelisation renaming (module Proof to ProofProp)
  open import RoutingLib.Asynchronous.Theorems.Core all-pairs-parallelisation using (iter; SynchronousConditions; Start)
  open import RoutingLib.Asynchronous.Theorems.UresinDubois1 𝕤 all-pairs-parallelisation
  
  D₀ : Pred lzero
  D₀ i = U

  x₀∈D₀ : x₀ ∈ D₀
  x₀∈D₀ i = U-Universal (x₀ i)

  D₀-subst : ∀ {x y} → x ≈ y → x ∈ D₀ → y ∈ D₀
  D₀-subst {_} {y} _ _ i = U-Universal (y i)

  D₀-closed : ∀ x → x ∈ D₀ → f x ∈ D₀
  D₀-closed x _ i = U-Universal (f x i)

  f-monotone : ∀ {x y} → x ∈ D₀ →  y ∈ D₀ → (∀ i → x i ≼ y i) →
               ∀ i → f x i ≼ f y i
  f-monotone {x} {y} x∈D₀ y∈D₀ x≼y i j =
    min∞[s]≤min∞[t] (x i j) (inj₁ (x≼y i j)) ≤-path-cost
    where
    ≤-path-cost : ∀ k → x i j ≤ path-cost y i j k ⊎
                         Σ (Fin n) (λ v → path-cost x i j v ≤ path-cost y i j k)
    ≤-path-cost k = inj₂ (k , path-cost-monotone x≼y i j k)

  iter-decreasing : ∀ K → iter x₀ (suc K) ≼ₘ iter x₀ K
  iter-decreasing zero i j = min∞[t]≤x (x₀ i j) (path-cost x₀ i j) (inj₁ ≤-refl)
  iter-decreasing (suc K) i = f-monotone
    (λ j → U-Universal (iter x₀ (suc K)))
    (λ j → U-Universal (iter x₀ K))
    (λ j → iter-decreasing K j) i

  iter-fixed : ∀ t → iter x₀ (suc t) ≡ₘ iter x₀ t → ∀ K →
               iter x₀ t ≈ iter x₀ (t +ℕ K)
  iter-fixed t iter≡ zero i j = cong (λ x → iter x₀ x i j) (sym (+-idʳℕ t))
  iter-fixed t iter≡ (suc K) i j = trans (sym (iter≡ i j))
    (subst (iter x₀ (suc t) i j ≡_)
      (cong (λ x → iter x₀ x i j) (sym (+ℕ-suc t K)))
      (iter-fixed (suc t) (f-cong iter≡) K i j)) 

  iter∞-dependent : ℕ → Set
  iter∞-dependent K = ∀ i j → iter x₀ K i j ≡ ∞ → iter x₀ (suc K) i j ≡ ∞

  iter∞-chain : ∀ K → iter∞-dependent K → iter∞-dependent (suc K)
  iter∞-chain K ⇒∞ i j iterᵢⱼsK≡∞ with iter x₀ (suc (suc K)) i j ≟ ∞
  ... | yes iterᵢⱼssK≡∞ = iterᵢⱼssK≡∞
  ... | no  iterᵢⱼssK≢∞  with min∞[t]∈t (iter x₀ (suc K) i j) (path-cost (iter x₀ (suc K)) i j)
  ...   | inj₁ iterᵢⱼ≡ = contradiction (trans iterᵢⱼ≡ iterᵢⱼsK≡∞) iterᵢⱼssK≢∞
  ...   | inj₂ (k , p) rewrite p with iter x₀ (suc K) i k ≟ ∞ | iter x₀ (suc K) k j ≟ ∞
  ...     | yes iterᵢₖsK≡∞ | _ rewrite iterᵢₖsK≡∞ = contradiction refl iterᵢⱼssK≢∞
  ...     | no  _         | yes iterₖⱼsK≡∞ rewrite iterₖⱼsK≡∞ = contradiction (+-comm (iter x₀ (suc K) i k) ∞) iterᵢⱼssK≢∞
  ...     | no  iterᵢₖsK≢∞ | no iterₖⱼsK≢∞ with iter x₀ K i k ≟ ∞ | iter x₀ K k j ≟ ∞
  ...       | yes iterᵢₖK≡∞ | _            = contradiction (⇒∞ i k iterᵢₖK≡∞) iterᵢₖsK≢∞
  ...       | no  _        | yes iterₖⱼK≡∞ = contradiction (⇒∞ k j iterₖⱼK≡∞) iterₖⱼsK≢∞
  ...       | no  iterᵢₖK≢∞ | no  iterₖⱼK≢∞ with ≢∞⇒≡N iterᵢₖK≢∞ | ≢∞⇒≡N iterₖⱼK≢∞
  ...         | xᵢₖ , pᵢₖ | xₖⱼ , pₖⱼ rewrite pᵢₖ | pₖⱼ = contradiction
                (min∞[t]≤x (iter x₀ K i j) (path-cost (iter x₀ K) i j)
                  (inj₂ (k , path-cost≤xᵢₖ+xₖⱼ)))
                iterᵢⱼsK≰xᵢₖ+xₖⱼ
                where
                iterᵢⱼsK≰xᵢₖ+xₖⱼ : iter x₀ (suc K) i j ≰ N (xᵢₖ +ℕ xₖⱼ)
                iterᵢⱼsK≰xᵢₖ+xₖⱼ = subst (_≰ N (xᵢₖ +ℕ xₖⱼ)) (sym iterᵢⱼsK≡∞) ∞≰

                path-cost≤xᵢₖ+xₖⱼ : path-cost (iter x₀ K) i j k ≤ N (xᵢₖ +ℕ xₖⱼ)
                path-cost≤xᵢₖ+xₖⱼ = ≤-reflexive (trans (cong (iter x₀ K i k +_) pₖⱼ)
                  (cong (_+ N xₖⱼ) pᵢₖ))


  FinPair : Setoid lzero lzero
  FinPair = setoid (Fin n × Fin n)

  open Memb FinPair using () renaming (_∈_ to _∈L_; _⊆_ to _⊆L_)

  is∞? : ∀ K → Decidable (λ node → iter x₀ K (proj₁ node) (proj₂ node) ≡ ∞)
  is∞? K = λ node → iter x₀ K (proj₁ node) (proj₂ node) ≟ ∞

  ∞-nodes : ℕ → List (Fin n × Fin n)
  ∞-nodes zero = dfilter (is∞? 0) (allFinPairs n)
  ∞-nodes (suc K) = dfilter (is∞? (suc K)) (∞-nodes K)

  node∈∞-nodes⇒node≡∞ : ∀ K i j → (i , j) ∈L ∞-nodes K → iter x₀ K i j ≡ ∞
  node∈∞-nodes⇒node≡∞ zero i j node∈ = proj₂ (∈-dfilter⁻ (is∞? 0)
    {i , j} {allFinPairs n} node∈)
  node∈∞-nodes⇒node≡∞ (suc K) i j node∈ = proj₂ (∈-dfilter⁻ (is∞? (suc K))
    {i , j} {∞-nodes K} node∈)

  node≡∞⇒node∈∞-nodes : ∀ K i j → iter x₀ K i j ≡ ∞ → (i , j) ∈L ∞-nodes K
  node≡∞⇒node∈∞-nodes zero i j iter≡∞ = ∈-dfilter⁺ (is∞? 0) iter≡∞
    (∈-allFinPairs⁺ i j)
  node≡∞⇒node∈∞-nodes (suc K) i j iter≡∞ with iter x₀ K i j ≟ ∞
  ... | yes ≡∞ =  ∈-dfilter⁺ (is∞? (suc K)) iter≡∞
    (node≡∞⇒node∈∞-nodes K i j ≡∞)
  ... | no  ≢∞ with ≢∞⇒≡N ≢∞
  ...   | _ , p = contradiction
    (iter-decreasing K i j)
    (subst₂ _≰_ (sym iter≡∞) (sym p) ∞≰)

  ∞-nodes-dec : ∀ K → ∞-nodes (suc K) ⊆L ∞-nodes K
  ∞-nodes-dec K x∈∞-nodes = proj₁ (∈-dfilter⁻ (is∞? (suc K)) x∈∞-nodes)

  ∞-nodes-length≡⇒∞-nodes≡ : ∀ K → length (∞-nodes K) ≡ length (∞-nodes (suc K)) →
                               ∞-nodes K ≡ ∞-nodes (suc K)
  ∞-nodes-length≡⇒∞-nodes≡ K length≡ = sym (|dfilter[xs]|≡|xs|⇒dfilter[xs]≡xs
    (is∞? (suc K)) (sym length≡))

  ∞-nodes≡⇒iterₖ≡∞⇒iterₛₖ≡∞ : ∀ K → ∞-nodes K ≡ ∞-nodes (suc K) →
                                iter∞-dependent K
  ∞-nodes≡⇒iterₖ≡∞⇒iterₛₖ≡∞ K ∞-nodes≡ i j iterₖ≡∞ =
    node∈∞-nodes⇒node≡∞ (suc K) i j (subst ((i , j) ∈L_) ∞-nodes≡
      (node≡∞⇒node∈∞-nodes K i j iterₖ≡∞))

  ∞-nodes≡+∈∞-nodes⇒iter≡∞ : ∀ K → ∞-nodes K ≡ ∞-nodes (suc K) →
                               {node : Fin n × Fin n} → node ∈L ∞-nodes (suc K) →
                               iter x₀ (suc (suc K)) (proj₁ node) (proj₂ node) ≡ ∞
  ∞-nodes≡+∈∞-nodes⇒iter≡∞ K ∞-nodes≡ {i , j} node∈ =
    iter∞-chain K (∞-nodes≡⇒iterₖ≡∞⇒iterₛₖ≡∞ K ∞-nodes≡) i j
      (node∈∞-nodes⇒node≡∞ (suc K) i j node∈)

  ∞-nodes-fixed-range : ∀ K → ∞-nodes K ≡ ∞-nodes (suc K) → ∀ t →
                        ∞-nodes K ≡ ∞-nodes (K +ℕ t)
  ∞-nodes-fixed-range K ∞-nodes≡ zero = cong ∞-nodes (sym (+-idʳℕ K))
  ∞-nodes-fixed-range K ∞-nodes≡ (suc t) = trans ∞-nodes≡
    (subst (∞-nodes (suc K) ≡_) (cong ∞-nodes (sym (+ℕ-suc K t)))
      (∞-nodes-fixed-range (suc K) ∞-nodesₛ≡ t))
    where
    ∞-nodesₛ≡ : ∞-nodes (suc K) ≡ ∞-nodes (suc (suc K))
    ∞-nodesₛ≡ = sym (dfilter[xs]≡xs (is∞? (suc (suc K)))
      (tabulateAll (∞-nodes≡+∈∞-nodes⇒iter≡∞ K ∞-nodes≡)))

  ∞-nodes-fixed : ∀ K → ∞-nodes K ≡ ∞-nodes (suc K) → ∀ {t} → K ≤ℕ t →
                  ∞-nodes t ≡ ∞-nodes (suc t)
  ∞-nodes-fixed K ∞-nodes≡ {t} K≤t = trans (sym (trans (∞-nodes-fixed-range K ∞-nodes≡ (t ∸ K)) (cong ∞-nodes (m+n∸m≡n K≤t))))
    (trans (∞-nodes-fixed-range K ∞-nodes≡ (suc t ∸ K)) (cong ∞-nodes (m+n∸m≡n {K} {suc t} (≤ℕ-step K≤t))))

  ∞-nodes-length-dec : ∀ K → length (∞-nodes (suc K)) ≤ℕ length (∞-nodes K)
  ∞-nodes-length-dec K = |dfilter[xs]|≤|xs| (is∞? (suc K)) (∞-nodes K)
  
  ∞-nodes-converge : ∀ {K} → Acc _<ℕ_ (length (∞-nodes K)) → ∃ λ T → ∀ {t} →
                     T ≤ℕ t → ∞-nodes t ≡ ∞-nodes (suc t)
  ∞-nodes-converge {K} (acc rs) with length (∞-nodes K) ≟ℕ length (∞-nodes (suc K))
  ... | yes ∞-nodes-length≡ = K ,
    ∞-nodes-fixed K (∞-nodes-length≡⇒∞-nodes≡ K ∞-nodes-length≡)
  ... | no  ∞-nodes-length≢ = ∞-nodes-converge {suc K} (rs (length (∞-nodes (suc K)))
    (≤+≢⇒ℕ< (∞-nodes-length-dec K) (∞-nodes-length≢ ∘ sym)))
  
  score : ℕ → ℕ
  score K = sum {n} (λ i → sum {n} (λ j → extractℕ (iter x₀ K i j)))

  module _ (∞-conv : ∃ λ T → ∀ {t} → T ≤ℕ t → ∞-nodes t ≡ ∞-nodes (suc t)) where
    extractℕ-dec : ∀ {K} → proj₁ ∞-conv ≤ℕ K → ∀ i j →
                   extractℕ (iter x₀ (suc K) i j) ≤ℕ extractℕ (iter x₀ K i j)
    extractℕ-dec {K} T≤K i j with iter x₀ (suc K) i j ≟ ∞ | iter x₀ K i j ≟ ∞
    ... | yes iterₛₖ≡∞ | yes iterₖ≡∞ rewrite iterₛₖ≡∞ | iterₖ≡∞ = ≤ℕ-refl
    ... | no  iterₛₖ≢∞ | yes iterₖ≡∞ = contradiction
      (∞-nodes≡⇒iterₖ≡∞⇒iterₛₖ≡∞ K (proj₂ ∞-conv T≤K) i j iterₖ≡∞) iterₛₖ≢∞
    ... | no  iterₛₖ≢∞ | no  iterₖ≢∞ =
                 ≤⇒extractℕ≤ iterₛₖ≢∞ iterₖ≢∞ (iter-decreasing K i j)
    ... | yes iterₛₖ≡∞ | no  iterₖ≢∞ with ≢∞⇒≡N iterₖ≢∞
    ...   | _ , p = contradiction
      (iter-decreasing K i j)
      (subst₂ _≰_ (sym iterₛₖ≡∞) (sym p) ∞≰)

    score-dec : ∀ {K} → proj₁ ∞-conv ≤ℕ K → score (suc K) ≤ℕ score K
    score-dec {K} T≤K = sum[s]≤sum[t]
              (λ i → sum[s]≤sum[t]
                (λ j → extractℕ-dec T≤K i j))

    extractℕ-dec-strict : ∀ {K} → proj₁ ∞-conv ≤ℕ K → ∀ i j →
                          iter x₀ (suc K) i j ≢ iter x₀ K i j →
                          extractℕ (iter x₀ (suc K) i j) <ℕ extractℕ (iter x₀ K i j)
    extractℕ-dec-strict {K} T≤K i j iter≢ = ≤+≢⇒ℕ< (extractℕ-dec T≤K i j) extractℕ≢
      where
      extractℕ≢ : extractℕ (iter x₀ (suc K) i j) ≢ extractℕ (iter x₀ K i j)
      extractℕ≢ with iter x₀ (suc K) i j ≟ ∞ | iter x₀ K i j ≟ ∞
      extractℕ≢ | yes iterₛₖ≡∞ | yes iterₖ≡∞ = contradiction (trans iterₛₖ≡∞ (sym iterₖ≡∞)) iter≢
      extractℕ≢ | yes iterₛₖ≡∞ | no  iterₖ≢∞ with ≢∞⇒≡N iterₖ≢∞
      ... | x , p = contradiction (iter-decreasing K i j) (subst₂ _≰_ (sym iterₛₖ≡∞) (sym p) ∞≰)
      extractℕ≢ | no  iterₛₖ≢∞ | yes iterₖ≡∞ = contradiction
                  (∞-nodes≡⇒iterₖ≡∞⇒iterₛₖ≡∞ K (proj₂ ∞-conv T≤K) i j iterₖ≡∞)
                  iterₛₖ≢∞
      extractℕ≢ | no  iterₛₖ≢∞ | no  iterₖ≢∞ = ≢⇒extractℕ≢ iterₛₖ≢∞ iterₖ≢∞ iter≢

    iter≉⇒score< : ∀ {t} → proj₁ (∞-conv) ≤ℕ t → iter x₀ (suc t) ≉ iter x₀ t →
                    score (suc t) <ℕ score t
    iter≉⇒score< {t} T≤t iter≉ with ≢ₘ-witness iter≉
    ... | i , j , iterᵢⱼ≢ = sum[s]<sum[t]
      ((λ i → sum[s]≤sum[t] (λ j → extractℕ-dec T≤t i j)))
      (i , sum[s]<sum[t]
        (λ j → extractℕ-dec T≤t i j)
        (j , extractℕ-dec-strict T≤t i j iterᵢⱼ≢))

    iter-fixed-point : ∀ {t} → proj₁ (∞-conv) ≤ℕ t → Acc _<ℕ_ (score t) →
                       ∃ λ T → ∀ K → iter x₀ T ≈ iter x₀ (T +ℕ K)
    iter-fixed-point {t} T≤t accₜ with iter x₀ (suc t) ≟ₘ iter x₀ t
    ... | yes iter≈ = t , iter-fixed t iter≈
    iter-fixed-point {t} T≤t (acc rs) | no iter≉ =
                     iter-fixed-point {suc t} (≤ℕ-step T≤t)
                       (rs (score (suc t)) (iter≉⇒score< T≤t iter≉))


  iter-converge : ∃ λ T → ∀ t → iter x₀ T ≈ iter x₀ (T +ℕ t)
  iter-converge with ∞-nodes-converge {0} (<-well-founded (length (∞-nodes 0)))
  ... | T∞ , ∞-conv = iter-fixed-point (T∞ , ∞-conv) (≤ℕ-refl)
                      (<-well-founded (score T∞))

  start : Start lzero
  start = record {
    x₀ = x₀ ;
    D₀ = D₀ ;
    x₀∈D₀ = x₀∈D₀ ;
    D₀-subst = D₀-subst ;
    D₀-closed = D₀-closed
    }

  poset : M-poset lzero
  poset = record {
    _≼ᵢ_ = λ {i} → _≼_ ;
    isPartialOrderᵢ = λ i → ≼-isPartialOrder
    }

  syncCond : SynchronousConditions lzero
  syncCond = record {
    start           = start ;
    poset           = poset ;
    f-monotone      = f-monotone ;
    iter-decreasing = iter-decreasing ;
    iter-converge   = iter-converge 
    }

  open ProofProp syncCond hiding (ξ)

  open Proof aco x₀∈D0

  converging-time : 𝕋
  converging-time = proj₁ async-converge

  converging-state : Matrix
  converging-state = ξ
