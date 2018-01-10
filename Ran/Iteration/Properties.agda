-- imports
open import Computation
  using (Computation; ACO)
open import Schedule
  using (Schedule)
open import Data.Nat
  using (ℕ; _+_; _≤_; zero; suc; _<_; _≟_; s≤s; z≤n; _∸_; _≤?_; pred)
open import Data.Fin
  using (Fin)
open import Relation.Binary
  using (Setoid; Rel; Reflexive; Antisymmetric; Transitive; IsEquivalence; _⇒_)
open import Data.Product
  using (∃; _,_; proj₂; proj₁; _×_)
open import Induction.Nat
  using (<-well-founded)
open import Relation.Unary
  using (_∈_; Pred; _∩_; _∉_)
open import Induction.WellFounded
  using (Acc; acc)
open import Data.Nat.Properties
  using (≤-trans; ≤-reflexive; +-identityʳ; m≤m+n; <⇒≤;
        <⇒≤pred; ≤+≢⇒<; m+n∸m≡n; ≤-antisym; pred-mono; +-suc)
open import Relation.Binary.PropositionalEquality
  using (cong₂; subst; _≡_; cong) renaming (refl to ≡refl; sym to ≡sym; trans to ≡trans)
open import Data.Fin.Dec
  using (_∈?_)
open import Relation.Nullary
  using (yes; no; ¬_)
open import Relation.Nullary.Negation
  using (contradiction)
open import Data.Fin.Subset
  using () renaming (_∈_ to _∈s_)
open import Function
  using (_∘_)
  
open Setoid
  using (Carrier; _≈_; isEquivalence)
open Data.Nat.Properties.≤-Reasoning
  using (_≤⟨_⟩_; begin_; _∎)

module Iteration.Properties {a}{ℓ}{n}{S : Fin n → Setoid a ℓ}
  (c : Computation S)(s : Schedule n) where

  open import Iteration s c
    using (async-iter)
  open Schedule.Schedule s
  open Schedule.Timing s
  open import Schedule.Properties s
    using (φ≤τ; τ-inc; nextActive-active; nextActiveφ<φs; prop1-iii)
  open Computation.Computation c
  open IsEquivalence

  φsK≤sk⇒τK≤βsK : ∀ k K i → φ (suc K) ≤ suc k → τ K i ≤ β (suc k) i
  φsK≤sk⇒τK≤βsK k K i p = subst ((τ K i) ≤_)
          (cong (λ x → β x i) (m+n∸m≡n p))
          (proj₂ (prop1-iii K i (suc k ∸ (φ (suc K)))))

  cong≈ : ∀ i {a} {A : Set a}
     (g : A → Carrier (S i)) {x y} → x ≡ y → (_≈_ (S i)) (g x) (g y)
  cong≈ i g {x} ≡refl = refl (isEquivalence (S i))

  module Theorem1 {x₀ : (i : Fin n) → Carrier (S i)}(aco : ACO c)(x₀∈D₀ : ∀ i → x₀ i ∈ (Computation.ACO.D aco) 0 i) where
    open Computation.ACO aco
  
    τK≤k⇒xₖ∈DK : ∀ k K i → τ K i ≤ k → (accₖ : Acc _<_ k) →
                           async-iter k x₀ accₖ i ∈ D K i
    τK≤k⇒xₖ∈DK zero K i τ≤k (acc rs) with M ≟ 0
    ... | no M≢0 = subst ((x₀ i) ∈_) (cong (λ k → D k i)
        (≤-antisym z≤n (subst (K ≤_) (≤-antisym τ≤k z≤n) (τ-inc K i))))
                  (x₀∈D₀ i)
    τK≤k⇒xₖ∈DK zero K i τ≤k (acc rs) | yes M≡0 with D-finish
    ...| (ξ , ξ∈D , x∈D⇒x≡ξ) =
               D-subst K i (ξ i) (x₀ i)
                 ((sym (isEquivalence (S i))) (x∈D⇒x≡ξ {x₀} 0 i
                 (subst (x₀ i ∈_) (cong (λ k → D k i) (≡sym (cong (_+ 0) M≡0)))
                   (x₀∈D₀ i))))
                  (subst (ξ i ∈_) (cong (λ k → D k i) (cong (_+ K) M≡0)) (ξ∈D K i))
    τK≤k⇒xₖ∈DK (suc k) K i τ≤sk (acc rs) with i ∈? α (suc k)
    τK≤k⇒xₖ∈DK (suc k) zero i τ≤sk (acc rs) | yes i∈α with M ≟ 0
    ... | no M≢0 with D-monotone 0 (≤+≢⇒< z≤n (M≢0 ∘ ≡sym))
    ... | ∈D1⇒∈D0 , _ = ∈D1⇒∈D0 i
                    (f (λ j → async-iter (β (suc k) j) x₀
                      (rs (β (suc k) j)
                      (s≤s (causality k j))) j) i)
                    (c-monotone 0
                    (λ j → τK≤k⇒xₖ∈DK (β (suc k) j) 0 j
                       z≤n
                       (rs (β (suc k) j) (s≤s (causality k j))))
                    i)
    τK≤k⇒xₖ∈DK (suc k) zero i τ≤sk (acc rs) | yes i∈α | yes M≡0 with D-finish
    ... | (ξ , ξ∈D , x∈D⇒x≡ξ) = D-subst 0 i (ξ i)
                          (f (λ j → async-iter (β (suc k) j) x₀
                            (rs (β (suc k) j) (s≤s (causality k j))) j) i)
                          ((sym (isEquivalence (S i)))
                            (x∈D⇒x≡ξ
                              {f (λ j → async-iter (β (suc k) j) x₀
                                (rs (β (suc k) j) (s≤s (causality k j))) j)}
                              1 i
                              (subst
                                ((f (λ j → async-iter (β (suc k) j) x₀
                                  (rs (β (suc k) j) (s≤s (causality k j))) j)
                                  i) ∈_)
                        (cong (λ t → D t i) (≡sym (cong (_+ 1) M≡0)))
                        (c-monotone 0 (λ j → τK≤k⇒xₖ∈DK (β (suc k) j) 0 j
                          z≤n
                          (rs (β (suc k) j) (s≤s (causality k j)))) i))))
                          (subst (ξ i ∈_) (cong (λ t → D t i) (cong (_+ 0) M≡0)) (ξ∈D 0 i))
    τK≤k⇒xₖ∈DK (suc k) (suc K) i τ≤sk (acc rs) | yes i∈α =
                    c-monotone K
                    (λ j → τK≤k⇒xₖ∈DK (β (suc k) j) K j
                      (φsK≤sk⇒τK≤βsK k K j (≤-trans (φ≤τ (suc K) i) τ≤sk))
                      (rs (β (suc k) j)
                      (s≤s (causality k j))))
                    i
    τK≤k⇒xₖ∈DK (suc k) K i τ≤sk (acc rs) | no  i∉α with τ K i  ≟ (suc k)
    ... | yes τK≡sk = contradiction (subst (i ∈s_) (cong α τK≡sk) (nextActive-active (φ K) i)) i∉α
    ... | no  τK≢sk = τK≤k⇒xₖ∈DK k K i
                    (<⇒≤pred (≤+≢⇒< τ≤sk τK≢sk)) (rs k (≤-reflexive ≡refl))
  
    -- Theorem 1
    theorem1-proof :  (K₁ : ℕ) (i : Fin n) → (S i ≈ async-iter (φ (suc M) + K₁) x₀
                   (<-well-founded (φ (suc M) + K₁)) i) (proj₁ D-finish i)
    theorem1-proof K₁ i with D-finish
    ... | (ξ , ξ∈D , x∈D⇒x≡ξ) = x∈D⇒x≡ξ
                   {async-iter (φ (suc M) + K₁) x₀
                     (<-well-founded (φ (suc M) + K₁))}
                   0 i (τK≤k⇒xₖ∈DK (φ (suc M) + K₁) (M + 0) i
                   (begin
                      τ (M + 0) i ≤⟨ ≤-reflexive (cong₂ τ (+-identityʳ M) ≡refl) ⟩
                      τ M i ≤⟨ <⇒≤ (nextActiveφ<φs M i) ⟩
                      φ (suc M) ≤⟨ m≤m+n (φ (suc M)) K₁ ⟩
                      φ (suc M) + K₁ ∎
                    )
                   (<-well-founded (φ (suc M) + K₁)))
                   
  
    theorem1 : ∃ λ K → ∀ K₁ i → (_≈_ (S i)) (async-iter (K + K₁) x₀
             (<-well-founded (K + K₁)) i) (proj₁ D-finish i)
    theorem1 = φ (suc M) , theorem1-proof


  y : ((i : Fin n) → Carrier (S i)) → ℕ → ((i : Fin n) → Carrier (S i))
  y x₀ zero = x₀
  y x₀ (suc K) = f (y x₀ K)


  -- Proposition 3
  module Proposition3 (D₀ : (i : Fin n) → Pred (Carrier (S i)) a)
               (x₀ : (i : Fin n) → Carrier (S i))
               ([_]_≼_ : (i : Fin n) → Rel (Carrier (S i)) a)
               (≼-refl : ∀ i → Reflexive [ i ]_≼_)
               (≼-reflexive : ∀ i → _≈_ (S i) ⇒ [ i ]_≼_)
               (≼-antisym : ∀ i → Antisymmetric (_≈_ (S i)) [ i ]_≼_)               
               (≼-trans : ∀ i → Transitive [ i ]_≼_)
               (x₀∈D₀ : ∀ i → x₀ i ∈ D₀ i)
               (D₀-subst : ∀ i x y → (_≈_ (S i)) x y → x ∈ D₀ i → y ∈ D₀ i)
               (closed : ∀ a → (∀ i → a i ∈ D₀ i) → (∀ i → f a i ∈ D₀ i))
               (y-converge : ∃ λ M → (∀ t i → (_≈_ (S i)) (y x₀ M i) (y x₀ (M + t) i)) ×
                           (∀ t → t < M → ∃ λ i → ¬ ((_≈_ (S i)) (y x₀ t i) (y x₀ (suc t) i))))
               (y-dec : ∀ K i → [ i ] (y x₀ (suc K) i) ≼ (y x₀ K i))
               (f-monotone : ∀ {a b} → (∀ i → a i ∈ D₀ i) × (∀ i → b i ∈ D₀ i) →
                             (∀ i → [ i ] a i ≼ b i) → (∀ i → [ i ] f a i ≼ f b i))
               where
               
    K≡t⇒yK≼yt : ∀ K t i → K ≡ t → [ i ] (y x₀ t i) ≼ (y x₀ K i)
    K≡t⇒yK≼yt K t i K≡t = ≼-reflexive i (cong≈ i (λ k → y x₀ k i) (≡sym K≡t))

    y-dec-full : ∀ K t i → K ≤ t → [ i ] (y x₀ t i) ≼ (y x₀ K i)
    y-dec-full K zero i K≤t = K≡t⇒yK≼yt K zero i (≤-antisym K≤t z≤n)
    y-dec-full K (suc t) i K≤t with (K ≟ suc t)
    ... | yes p = K≡t⇒yK≼yt K (suc t) i p
    ... | no ¬p = (≼-trans i) (y-dec t i)
                  (y-dec-full K t i (pred-mono (≤+≢⇒< K≤t ¬p)))

    M : ℕ
    M = proj₁ y-converge

    ξ : (i : Fin n) → Carrier (S i)
    ξ = y x₀ M

    D : ℕ → ∀ i → Pred (Carrier (S i)) a
    D K i = (λ a → (([ i ] ξ i ≼ a) × ([ i ] a ≼ y x₀ K i))) ∩ (D₀ i)

    D-subst : ∀ K i x z → (_≈_ (S i)) x z → x ∈ D K i → z ∈ D K i
    D-subst K i x z x≡z ((ξ≼x , x≼yK) , x∈D₀) =
                  (≼-trans i ξ≼x (≼-reflexive i x≡z) ,
                  ≼-trans i (≼-reflexive i ((sym (isEquivalence (S i))) x≡z)) x≼yK) ,
                  D₀-subst i x z x≡z x∈D₀

    DsK⊆DK : ∀ K i (dᵢ : Carrier (S i)) → dᵢ ∈ D (suc K) i → dᵢ ∈ D K i
    DsK⊆DK K i dᵢ ((ξ≼dᵢ , dᵢ≼yK ), dᵢ∈D₀) =
                  (ξ≼dᵢ , (≼-trans i) dᵢ≼yK (y-dec K i)) , dᵢ∈D₀

    closed-trans : ∀ K i → y x₀ K i ∈ D₀ i
    closed-trans zero i = x₀∈D₀ i
    closed-trans (suc K) i = closed (y x₀ K) (closed-trans K) i

    yK∈DK : ∀ K i → K < M → (y x₀ K i) ∈ D K i
    yK∈DK K i K<M = (y-dec-full K M i (<⇒≤ K<M) , ≼-refl i) ,
                     closed-trans K i

    yK∉DsK : ∀ K → K < M → ∃ λ i → (y x₀ K i) ∉ D (suc K) i
    yK∉DsK K K<M with proj₂ y-converge
    yK∉DsK K K<M | fixed , first with first K K<M
    ... | i , p = i , λ y∈D → contradiction
                      (≼-antisym i (proj₂ (proj₁ y∈D)) (y-dec K i))
                      p

    fξ≡ξ : ∀ i → (_≈_ (S i)) (f ξ i) (ξ i)
    fξ≡ξ i with isEquivalence (S i)
    ... | isEq = (sym isEq) ((trans isEq) (proj₁ (proj₂ y-converge) 1 i)
                (cong≈ i (λ k → y x₀ k i)
                (≡trans (+-suc M 0) (cong suc (+-identityʳ M)))))

    x₀∈D0 : ∀ i → x₀ i ∈ D 0 i
    x₀∈D0 i = (y-dec-full zero (proj₁ y-converge) i z≤n , ≼-refl i) , x₀∈D₀ i

    

    D-monotone : ∀ K → K < M → (∀ i →
                 (∀ (dᵢ : Carrier (S i)) → dᵢ ∈ D (suc K) i → dᵢ ∈ D K i)) ×
                 (∃ λ i → ∃ λ dᵢ' → dᵢ' ∈ D K i × dᵢ' ∉ D (suc K) i)
    D-monotone K K<M with yK∉DsK K K<M
    ... | i , p = (λ i dᵢ dᵢ∈DsK → DsK⊆DK K i dᵢ dᵢ∈DsK) , i , y x₀ K i , yK∈DK K i K<M , p



    D-finish : ∃ λ (ξ : (i : Fin n) → Carrier (S i)) → (∀ K i → ξ i ∈ D (M + K) i) ×
                            (∀ {x : (i : Fin n) → Carrier (S i)} K i → x i ∈ D (M + K) i →
                            (_≈_ (S i)) (x i) (ξ i))
    D-finish = y x₀ M ,
               (λ K i → (≼-refl i ,
                         ≼-reflexive i (proj₁ (proj₂ y-converge) K i)) ,
                         closed-trans M i) ,
               λ K i x∈D → ≼-antisym i (≼-trans i (proj₂ (proj₁ x∈D))
                 (y-dec-full M (M + K) i (m≤m+n M K))) (proj₁ (proj₁ x∈D))

    c-monotone : ∀ K → {x : ∀ i → Carrier (S i)} → (∀ i → x i ∈ D K i) →
                 (∀ i → f x i ∈ D (suc K) i)
    c-monotone K {x} x∈D i =
                 (≼-trans i
                   (≼-reflexive i ((sym (isEquivalence (S i))) (fξ≡ξ i)))
                   (f-monotone
                     ((λ j → closed-trans M j) , (λ j → proj₂ (x∈D j)))
                     (λ j → proj₁ (proj₁ (x∈D j))) i) ,
                 f-monotone ((λ j → proj₂ (x∈D j)) ,
                 λ j → closed-trans K j) (λ j → proj₂ (proj₁ (x∈D j))) i) ,
                 closed x (λ j → proj₂ (x∈D j)) i

    aco : ACO c
    aco = record {
      M = M ;
      D = D ;
      D-monotone = D-monotone ;
      D-finish = D-finish ;
      c-monotone = c-monotone ;
      D-subst = D-subst
      }

