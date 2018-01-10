-- imports
open import Schedule
  using (Schedule; 𝕋)
open import Computation
  using (Computation)
open import Data.Fin
  using (Fin; toℕ) renaming (zero to fzero; suc to fsuc; pred to fpred)
open import Relation.Binary
  using (Setoid; Decidable)
open import NatInf
open import NatInf.Properties
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; subst; cong; sym; trans; subst₂)
open import Relation.Unary
  using (Pred; U; _∈_; U-Universal; _∉_; ∅)
open import Level
  using () renaming (zero to lzero; suc to lsuc)
open import Data.Product
  using (_×_; _,_; ∃; proj₁; proj₂)
open import Functions
  using (min∞; max; sum)
open import Functions.Properties
  using (min∞-monotone; min∞-dec; x≤sum; sum-inc; sum-inc-strict; sum-limit; max-inc)
open import Data.Nat
  using (ℕ; zero; suc; _*_) renaming (_+_ to _+ℕ_; _≤_ to _≤ℕ_; _<_ to _<ℕ_; z≤n to z≤ℕn;
        s≤s to s≤ℕs; _≟_ to _≟ℕ_; _≤?_ to _≤ℕ?_)
open import Data.Nat.Properties
  using (+-suc; <⇒≢; ≤+≢⇒<; 1+n≰n; *-identityˡ; *-mono-≤; *-identityʳ)
  renaming (+-identityʳ to +-idʳℕ; ≤-trans to ≤ℕ-trans; ≤-reflexive to ≤ℕ-reflexive; n≤1+n to n≤ℕ1+n; <⇒≤ to <ℕ⇒≤ℕ)
open import Data.Sum
  using(_⊎_; inj₁; inj₂)
open import Relation.Nullary
  using (yes; no; ¬_; Dec)
open import Relation.Nullary.Negation
  using (contradiction)
open import Function
  using (_∘_)
open import Induction.WellFounded
  using (Acc; acc)
open import Induction.Nat
  using (<-well-founded)
open import Data.Fin.Subset
  using (Subset; ⊥; _∪_; ⊤; ⁅_⁆; _⊆_; ⋃)
open import Data.Fin.Subset.Properties
  using (⊥⊆; ⊆⊤; p⊆p∪q; poset)
open import Data.List
  using (List; []; _∷_; map; allFin; _++_; foldr; filter; length)
open import Algebra.FunctionProperties
  using (Op₂)
open import Relation.Nullary.Decidable
  using (⌊_⌋)
open import Data.Fin.Properties
  using (suc-injective)
open import Data.List.Properties
  using (length-filter)

open Setoid
  using (Carrier; _≈_)

module AllPairs.Convergence {n}(s : Schedule n)(x₀ : Fin n → (Fin n → ℕ∞))
  (Cᵢ,ᵢ : ∀ (i : Fin n) → x₀ i i ≡ N 0) where

  open import AllPairs n
  open import AllPairs.Properties n
  open Schedule.Schedule s
  open import Iteration s all-pairs-comp
    using (async-iter)
  open import Iteration.Properties all-pairs-comp s as iter-prop
    using (y; cong≈)
    
  
  D₀ : Fin n → Pred (Fin n → ℕ∞) lzero
  D₀ i = U

  D₀-subst : ∀ i x y → x ≡ᵣ y → x ∈ D₀ i → y ∈ D₀ i
  D₀-subst i _ z _ _ = U-Universal y

  x₀∈D₀ : ∀ i → x₀ i ∈ D₀ i
  x₀∈D₀ i = U-Universal (x₀ i)

  closed : ∀ a → (∀ i → a i ∈ D₀ i) → (∀ i → f a i ∈ D₀ i)
  closed a a∈D₀ i = U-Universal (f a i)

  f-monotone : ∀ {a b} → (∀ i → a i ∈ D₀ i) × (∀ i → b i ∈ D₀ i) →
               (∀ i → [ i ] a i ≼ b i) → (∀ i → [ i ] f a i ≼ f b i)
  f-monotone _ a≼b i j = min∞-monotone ((path-cost-monotone (λ x y → a≼b x y) i) j)


  y-dec : ∀ K → y x₀ (suc K) ≼ₘ y x₀ K
  y-dec zero i j = subst (min∞ (path-cost x₀ i j) ≤_)
                (sym (trans (sym (+-identityˡ (x₀ i j))) (cong (_+ (x₀ i j)) (sym (Cᵢ,ᵢ i)))))
                (min∞-dec (path-cost x₀ i j) i)
  y-dec (suc K) i = f-monotone
                ((λ j → U-Universal (y x₀ (suc K))) , ((λ j → U-Universal (y x₀ K))))
                (λ j → y-dec K j) i

  y-fixed : ∀ t → y x₀ t ≡ₘ y x₀ (suc t) → ∀ k → y x₀ t ≡ₘ y x₀ (t +ℕ k)
  y-fixed t yt≡yst zero i j = subst (y x₀ t i j ≡_)
      (cong (λ x → y x₀ x i j) (sym (+-idʳℕ t))) refl
  y-fixed t yt≡yst (suc k) i j = trans (yt≡yst i j)
      (subst (y x₀ (suc t) i j ≡_)
        (cong (λ x → y x₀ x i j) (sym (+-suc t (k))))
        (y-fixed (suc t) (congₘ yt≡yst) k i j))

  combine : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c}
         → (A → B → C) → List A → List B → List C
  combine f [] _ = []
  combine f (x ∷ xs) ys = map (f x) ys ++ combine f xs ys

  allFinPairs : ∀ n → List (Fin n × Fin n)
  allFinPairs n = combine _,_ (allFin n) (allFin n)

  _⊓ᵢⱼ_[_] : ∀ (x₁ x₂ : Fin n × Fin n) → ℕ → Fin n × Fin n
  (i₁ , j₁) ⊓ᵢⱼ (i₂ , j₂) [ K ] with ⊓-sel (y x₀ K i₁ j₁) (y x₀ K i₁ j₁)
  ... | inj₁ _ = i₁ , j₁
  ... | inj₂ _ = i₁ , j₁

  min-node : ℕ → List (Fin n × Fin n) → Fin n × Fin n → Fin n × Fin n
  min-node K nodes ⊤ = foldr _⊓ᵢⱼ_[ K ] ⊤ nodes

  _≟ᵢ_ : ∀ {m} → Decidable {A = Fin m} _≡_
  fzero ≟ᵢ fzero = yes refl
  fzero ≟ᵢ fsuc j = no (λ ())
  fsuc i ≟ᵢ fzero = no (λ ())
  fsuc i ≟ᵢ fsuc j with i ≟ᵢ j
  ... | yes refl = yes refl
  ... | no ¬p = no (¬p ∘ (λ p → suc-injective p))

  ≡ₙ-dist : ∀ {m}{i₁ j₁ i₂ j₂ : Fin m} → (i₁ , j₁) ≡ (i₂ , j₂) → i₁ ≡ i₂ × j₁ ≡ j₂
  ≡ₙ-dist refl = refl , refl

  _≟ₙ_ : Decidable {A = Fin n × Fin n} _≡_
  (i₁ , j₁) ≟ₙ (i₂ , j₂) with i₁ ≟ᵢ i₂ | j₁ ≟ᵢ j₂
  ... | yes p₁ | yes p₂ = yes (trans (cong (i₁ ,_) p₂) (cong (_, j₂) p₁))
  ... | yes _ | no ¬p = no (¬p ∘ λ x → proj₂ (≡ₙ-dist x))
  ... | no ¬p | _ = no (¬p ∘ λ x → proj₁ (≡ₙ-dist x))

  loose-nodes : ℕ → List (Fin n × Fin n)
  loose-nodes zero = allFinPairs n
  loose-nodes (suc K) = filter
                   (λ node → ⌊ node ≟ₙ min-node K (loose-nodes K) node ⌋)
                   (loose-nodes K)

  loose-nodes-dec : ∀ K → length (loose-nodes (suc K)) ≤ℕ length (loose-nodes K)
  loose-nodes-dec K = length-filter
                  (λ node → ⌊ node ≟ₙ min-node K (loose-nodes K) node ⌋)
                  (loose-nodes K)

  {-y≢⇒length< : ∀ t → y x₀ (suc t) ≢ₘ y x₀ t →
                length (loose-nodes (suc t)) <ℕ length (loose-nodes t)
  y≢⇒length< t yst≢yt = {!!}

  isFixed : ∀ K node → Set
  isFixed K (i , j) = ∀ t → y x₀ K i j ≡ y x₀ (K +ℕ t) i j

  fixed-nodes : ℕ → Fin n → Subset n
  fixed-nodes zero i = ⊥
  fixed-nodes (suc K) i = ⋃ ((fixed-nodes K i) ∷ map {!!} (allFin n))

  Z : ∀ K i j → y x₀ K i j ≢ y x₀ (suc K) i j → ∃ λ k → y x₀ K i j < y x₀ K i k
  Z K i j yK≢ysK = {!!}-}





  private
    x₀-sum : ℕ
    x₀-sum = suc (max {n} (λ i → max {n} (λ j → extractℕ (x₀ i j))) * n)
    -- x₀-sum = suc (sum {n} (λ i → sum {n} (λ j → extractℕ (x₀ i j))))

  extract : ∀ {x} → x ≢ ∞ → ∃ λ m → x ≡ N m
  extract {∞} x≢∞ = contradiction refl x≢∞
  extract {N x} x≢∞ = x , refl

  distance : ℕ → Fin n → Fin n → ℕ
  distance t i j with y x₀ t i j ≟ ∞
  ... | yes ≡∞ = x₀-sum 
  ... | no ≢∞ with extract ≢∞
  ... | x , _ = x

  m≢0⇒1≤m : ∀ {m} → m ≢ 0 → 1 ≤ℕ m
  m≢0⇒1≤m {zero} m≢0 = contradiction refl m≢0
  m≢0⇒1≤m {suc m} m≢0 = s≤ℕs z≤ℕn

  x₀≡∞⊎x₀<x₀-sum : ∀ i j → x₀ i j ≡ ∞ ⊎ x₀ i j < N (x₀-sum)
  x₀≡∞⊎x₀<x₀-sum i j with x₀ i j ≟ ∞
  ... | yes p = inj₁ p
  ... | no ¬p with n ≟ℕ 0
  x₀≡∞⊎x₀<x₀-sum () j | no ¬p | yes refl
  x₀≡∞⊎x₀<x₀-sum i j | no ¬p | no n≢0 with ≢∞⇒≡N ¬p
  ... | x , x₀≡x = inj₂ (subst (_< N (x₀-sum)) (sym x₀≡x) (s≤s (≤ℕ⇒≤
          (≤ℕ-trans
            (subst (_≤ℕ max {n} (λ j₁ → extractℕ (x₀ i j₁)))
              (cong extractℕ x₀≡x)
              (max-inc {n} (λ j₁ → extractℕ (x₀ i j₁)) j))
            (≤ℕ-trans (max-inc {n} (λ i₁ → max {n} (λ j₁ → extractℕ (x₀ i₁ j₁))) i)
            (≤ℕ-trans
              (≤ℕ-reflexive (sym (*-identityʳ (max {n} (λ i₁ → max {n} (λ j₁ → extractℕ (x₀ i₁ j₁)))))))
              (*-mono-≤ (≤ℕ-reflexive {max {n} (λ i₁ → max {n} (λ j₁ → extractℕ (x₀ i₁ j₁)))} refl) (m≢0⇒1≤m n≢0))))))))

  distanceₘ : ℕ → ℕ
  distanceₘ t = sum {n} (λ i → sum {n} (λ j → distance t i j))

  Z : ∀ t i j → y x₀ t i j ≢ ∞ → y x₀ t i j < N x₀-sum
  Z zero i j x₀≢∞ with x₀≡∞⊎x₀<x₀-sum i j
  ... | inj₁ x₀≡∞ = contradiction x₀≡∞ x₀≢∞
  ... | inj₂ <sum = <sum
  Z (suc t) i j yst≢∞ with y x₀ t i j ≟ ∞
  ... | yes yt≡∞ = {!!}
  ... | no  yt≢∞ with extract yst≢∞ 
  ... | x , yst≡x  = subst (_< N x₀-sum) (sym yst≡x)
                  (≤+<⇒< (subst (_≤ y x₀ t i j) yst≡x (y-dec t i j)) (Z t i j yt≢∞))

  dis-dec : ∀ t i j → distance (suc t) i j ≤ℕ distance t i j
  dis-dec t i j with y x₀ (suc t) i j ≟ ∞ | y x₀ t i j ≟ ∞
  dis-dec t i j | yes p | yes p₁ = ≤ℕ-reflexive refl
  dis-dec t i j | yes p | no ¬p with extract ¬p
  ... | x , yt≡x = contradiction (y-dec t i j) (subst (_≰ y x₀ t i j) (sym p)
                                 (subst (∞ ≰_) (sym yt≡x) ∞≰))
  dis-dec t i j | no ¬p | yes p with extract ¬p
  ... | x , yst≡x = ≤⇒≤ℕ (subst (_≤ N x₀-sum) yst≡x (<⇒≤ (Z (suc t) i j ¬p)))
  dis-dec t i j | no ¬p | no ¬p₁ with extract ¬p | extract ¬p₁
  ... | x₁ , yst≡x₁ | x₂ , yt≡x₂ = ≤⇒≤ℕ (subst₂ _≤_ yst≡x₁ yt≡x₂ (y-dec t i j))

  y≢⇒dis≢ : ∀ t i j → y x₀ (suc t) i j ≢ y x₀ t i j → distance (suc t) i j ≢ distance t i j
  y≢⇒dis≢ t i j yst≢yt with y x₀ (suc t) i j ≟ ∞ | y x₀ t i j ≟ ∞
  y≢⇒dis≢ t i j yst≢yt | yes p | yes p1 = contradiction (trans p (sym p1)) yst≢yt
  y≢⇒dis≢ t i j yst≢yt | yes p | no p1 with extract p1
  ... | x , yt≡x = ≢⇒≢ℕ (<+≢∞⇒≢ (subst (_< N x₀-sum) yt≡x (Z t i j p1))) ∘ sym
  y≢⇒dis≢ t i j yst≢yt | no p | yes p1 with extract p
  ... | x , yst≡x = ≢⇒≢ℕ (<+≢∞⇒≢ (subst (_< N x₀-sum) yst≡x (Z (suc t) i j p)))
  y≢⇒dis≢ t i j yst≢yt | no p | no p1 with extract p | extract p1
  ... | x₁ , yst≡x₁ | x₂ , yt≡x₂ with x₁ ≟ℕ x₂
  ... | yes refl = contradiction (trans yst≡x₁ (sym yt≡x₂)) yst≢yt
  ... | no  ¬p = ¬p

  disₘ-dec : ∀ t → distanceₘ (suc t) ≤ℕ distanceₘ t
  disₘ-dec t = sum-inc (λ i → sum-inc (λ j → dis-dec t i j))

  y≢⇒dis< : ∀ t → y x₀ (suc t) ≢ₘ y x₀ t → distanceₘ (suc t) <ℕ distanceₘ t
  y≢⇒dis< t yst≢yt with ≢ₘ-witness yst≢yt
  ... | i' , j' , p = sum-inc-strict (λ i → sum-inc (λ j → dis-dec t i j))
                (i' , sum-inc-strict ((λ j → dis-dec t i' j))
                (j' , ≤+≢⇒< (dis-dec t i' j') (y≢⇒dis≢ t i' j' p)))

  y-fixed-point : ∀ t → Acc _<ℕ_ (distanceₘ t) → ∃ λ M → ∀ k → y x₀ M ≡ₘ y x₀ (M +ℕ k)
  y-fixed-point t (acc rs) with y x₀ (suc t) ≟ₘ y x₀ t
  ... | yes p = t , y-fixed t (symₘ p)
  ... | no ¬p = y-fixed-point (suc t) (rs (distanceₘ (suc t)) (y≢⇒dis< t ¬p))

  y-fixed-point-inc : ∀ t → (accₜ : Acc _<ℕ_ (distanceₘ t)) → t ≤ℕ proj₁ (y-fixed-point t accₜ)
  y-fixed-point-inc t (acc rs) with y x₀ (suc t) ≟ₘ y x₀ t
  ... | yes p = ≤ℕ-reflexive refl
  ... | no ¬p = ≤ℕ-trans (n≤ℕ1+n t) (y-fixed-point-inc (suc t)
              (rs (distanceₘ (suc t)) (y≢⇒dis< t ¬p)))

  y-fixed-point-acc-irrelevant : ∀ t (a b : Acc _<ℕ_ (distanceₘ t)) →
                                 proj₁ (y-fixed-point t a) ≡ proj₁ (y-fixed-point t b)
  y-fixed-point-acc-irrelevant t (acc a) (acc b) with y x₀ (suc t) ≟ₘ y x₀ t
  ... | yes p = refl
  ... | no ¬p = y-fixed-point-acc-irrelevant (suc t)
                          (a (distanceₘ (suc t)) (y≢⇒dis< t ¬p))
                          (b (distanceₘ (suc t)) (y≢⇒dis< t ¬p))

  y-fixed-point-mono : ∀ t → (accₜ : Acc _<ℕ_ (distanceₘ t)) →
                       proj₁ (y-fixed-point t accₜ) ≤ℕ proj₁ (y-fixed-point (suc t)
                       (<-well-founded (distanceₘ (suc t))))
  y-fixed-point-mono t (acc rs) with y x₀ (suc t) ≟ₘ y x₀ t
  ... | yes p = ≤ℕ-trans (n≤ℕ1+n t) (y-fixed-point-inc (suc t)
                (<-well-founded (distanceₘ (suc t))))
  ... | no ¬p = ≤ℕ-reflexive (y-fixed-point-acc-irrelevant (suc t)
                (rs (distanceₘ (suc t)) (y≢⇒dis< t ¬p))
                (<-well-founded (distanceₘ (suc t))))

  y-fixed-first : ∀ t → proj₁ (y-fixed-point 0 (<-well-founded (distanceₘ 0))) ≤ℕ
                  proj₁ (y-fixed-point t (<-well-founded (distanceₘ t)))
  y-fixed-first zero = ≤ℕ-reflexive refl
  y-fixed-first (suc t) = ≤ℕ-trans (y-fixed-first t)
                     (y-fixed-point-mono t (<-well-founded (distanceₘ t)))

  ≢ₘ⇒∃≢ᵣ : ∀ t → y x₀ t ≢ₘ y x₀ (suc t) → ∃ λ i → y x₀ t i ≢ᵣ y x₀ (suc t) i
  ≢ₘ⇒∃≢ᵣ t yt≢yst with ≢ₘ-witness yt≢yst
  ... | i , j , p = i , ≢ᵣ-from-witness (j , p)

  y≡⇒dis≡t : ∀ t → y x₀ (suc t) ≡ₘ y x₀ t →
                   proj₁ (y-fixed-point t (<-well-founded (distanceₘ t))) ≡ t
  y≡⇒dis≡t t yst≡yt with y x₀ (suc t) ≟ₘ y x₀ t
  ... | yes p = refl
  ... | no ¬p = contradiction yst≡yt ¬p

  t<M⇒yt≢yst : ∀ t → t <ℕ proj₁ (y-fixed-point 0 (<-well-founded (distanceₘ 0))) →
               ∃ λ i → y x₀ t i ≢ᵣ y x₀ (suc t) i
  t<M⇒yt≢yst t t<M with y x₀ (suc t) ≟ₘ y x₀ t
  ... | yes p = contradiction (≤ℕ-trans t<M
        (subst ((proj₁ (y-fixed-point 0 (<-well-founded (distanceₘ 0))))≤ℕ_)
        (y≡⇒dis≡t t p) (y-fixed-first t))) 1+n≰n
  ... | no ¬p = ≢ₘ⇒∃≢ᵣ t (¬p ∘ symₘ)

  y-converge : ∃ λ M → ((∀ t i → ((y x₀ M i) ≡ᵣ (y x₀ (M +ℕ t) i))) ×
               (∀ t → t <ℕ M → ∃ λ i → (y x₀ t i) ≢ᵣ (y x₀ (suc t) i)))
  y-converge = proj₁ (y-fixed-point 0 (<-well-founded (distanceₘ 0))) ,
               proj₂ (y-fixed-point 0 (<-well-founded (distanceₘ 0))) ,
               t<M⇒yt≢yst

  open iter-prop.Proposition3 D₀ x₀ [_]_≼_ ≼-refl ≼-reflexive ≼-antisym ≼-trans x₀∈D₀ D₀-subst
                                 closed y-converge y-dec f-monotone
       using (aco; x₀∈D0; ξ)

  open iter-prop.Theorem1 {x₀} aco x₀∈D0

  convergence : 𝕋
  convergence = proj₁ theorem1

  result : Fin n → Fin n → ℕ∞
  result = ξ
