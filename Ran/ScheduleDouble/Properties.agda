-- imports
open import Data.Nat
  using (ℕ; zero; suc; _<_; _+_; _≤_; s≤s; z≤n; _∸_)
open import ScheduleDouble
  using (ScheduleDouble)
open import Data.Product
  using (proj₁; _,_; ∃; _×_)
open import Data.Nat.Properties
  using (m≤m+n; m+n∸m≡n; n≤1+n; ≤-reflexive; ≤-trans; <⇒≤; ≤+≢⇒<)
open import Data.Fin
  using (Fin; toℕ; inject₁; fromℕ; inject≤) renaming (zero to fzero; suc to fsuc)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; _≢_; subst; cong; sym; trans)
open import Data.Fin.Subset
  using (_∈_)
open import Induction.WellFounded
  using (Acc; acc)
open import Induction.Nat
  using (<-well-founded)
open import Data.Fin.Dec
  using (_∈?_)
open import Relation.Nullary
  using (yes; no)
open import Data.Fin.Subset.Properties
  using (∈⊤)
open import Functions
  using (max)
open import Functions.Properties
  using (max≤; max-inc; max-inc=n; m≤n⇒maxₘ≤maxₙ; max-mono)
open import Function
  using (_∘_)
open import Data.Fin.Properties
  using (inject₁-lemma; to-from; inject≤-lemma)

open Data.Nat.Properties.≤-Reasoning
  using (_≤⟨_⟩_; begin_; _∎)
  
module ScheduleDouble.Properties {n : ℕ}(s : ScheduleDouble n) where
  open ScheduleDouble.ScheduleDouble s
  open ScheduleDouble.Timing s
  
  -- general property
  ∀≢⇒< : ∀ t k → (∀ (t' : Fin (suc t)) → k ≢ (toℕ t')) → t < k
  ∀≢⇒< zero k p = ≤+≢⇒< z≤n ((p fzero) ∘ sym)
  ∀≢⇒< (suc t) k p = ≤+≢⇒<
       (∀≢⇒< t k (λ t' → subst (k ≢_) (inject₁-lemma t') (p (inject₁ t'))))
       (subst (k ≢_) (to-from (suc t)) (p (fromℕ (suc t))) ∘ sym)

  -- properties of finite
  finite-inc : ∀ t i j → t ≤ t + proj₁ (finite t i j)
  finite-inc t i j = m≤m+n t (proj₁ (finite t i j))

  finite-fin : ∀ t k i j → (t' : Fin (suc t)) →
              (toℕ t') + proj₁ (finite (toℕ t') i j) ≤ k →
              β k i j ≢ toℕ t'
  finite-fin t k i j t' p  with finite (toℕ t') i j
  ... | (m , q) = subst (_≢ toℕ t')
        (cong (λ x → β x i j) (m+n∸m≡n p))
        (q (k ∸ (toℕ t' + m)))

  -- Properties of nextActive'
  nextActive'-inc : ∀ t k i (p : i ∈ α (t + suc k))(rs : Acc _<_ k) →
                    t ≤ proj₁ (nextActive' t k i p rs)
  nextActive'-inc t zero i p _ = n≤1+n t
  nextActive'-inc t (suc k) i p (acc rs) with i ∈? α t
  ... | yes i∈α = ≤-reflexive refl
  ... | no  i∉α = ≤-trans (n≤1+n t)
                  (nextActive'-inc (suc t) k i (∈-α-comm t (suc k) i p)
                    (rs k (≤-reflexive refl)))

  -- Properties of nextActive
  nextActive-inc : ∀ t i → t ≤ nextActive t i
  nextActive-inc zero i = z≤n
  nextActive-inc (suc t) i with nonstarvation (suc t) i
  ... | k , p = nextActive'-inc (suc t) k i p (<-well-founded k)

  nextActive-active : ∀ t i → i ∈ α (nextActive t i)
  nextActive-active zero i = subst (i ∈_) (sym α₀) ∈⊤
  nextActive-active (suc t) i with nonstarvation (suc t) i
  ... | k , p with nextActive' (suc t) k i p (<-well-founded k)
  ... | _ , active = active

  -- Properties of expiryᵢⱼ
  expiryᵢⱼ-inc : ∀ t i j → t ≤ expiryᵢⱼ t i j
  expiryᵢⱼ-inc t i j = max-inc=n
               (λ x → (toℕ x) + proj₁ (finite (toℕ x) i j))
               (λ x → finite-inc (toℕ x) i j)

  expiryᵢⱼ-monotone : ∀ {t k} i j → t ≤ k → expiryᵢⱼ t i j ≤ expiryᵢⱼ k i j
  expiryᵢⱼ-monotone {t} {k} i j t≤k = m≤n⇒maxₘ≤maxₙ {suc t} {suc k}
                    {λ x → (toℕ x) + proj₁ (finite (toℕ x) i j)}
                    {λ x → (toℕ x) + proj₁ (finite (toℕ x) i j)}
                    (s≤s t≤k)
                    λ x → ≤-reflexive (trans
                      (cong (_+ proj₁ (finite (toℕ x) i j))
                        (sym (inject≤-lemma x (s≤s t≤k))))
                      (cong (toℕ (inject≤ x (s≤s t≤k)) +_)
                        (cong (λ y → proj₁ (finite y i j))
                          (sym (inject≤-lemma x (s≤s t≤k))))))

  -- Properties of expiryᵢ
  expiryᵢⱼ≤expiryᵢ : ∀ t i j → expiryᵢⱼ t i j ≤ expiryᵢ t i
  expiryᵢⱼ≤expiryᵢ t i j = max-inc (expiryᵢⱼ t i) j

  expiryᵢ-inc : ∀ t i → t ≤ expiryᵢ t i
  expiryᵢ-inc t i = max≤ (expiryᵢⱼ-inc t i)

  expiryᵢ-monotone : ∀ {t k} i → t ≤ k → expiryᵢ t i ≤ expiryᵢ k i
  expiryᵢ-monotone i t≤k = max-mono (λ j → expiryᵢⱼ-monotone i j t≤k)

 
  -- Properties of expiry
  expiryᵢ≤expiry : ∀ t i → expiryᵢ t i ≤ expiry t 
  expiryᵢ≤expiry t i = max-inc (expiryᵢ t) i

  expiry-inc : ∀ t → t ≤ expiry t
  expiry-inc t = max≤ (expiryᵢ-inc t)

  expiryₜ≤k⇒t≤βk : ∀ t k i j → expiry t ≤ k → t ≤ β k i j
  expiryₜ≤k⇒t≤βk t k i j expiryₜ≤k = <⇒≤ (∀≢⇒< t (β k i j)
                 (λ t' → finite-fin t k i j t' (begin
                   (toℕ t') + proj₁ (finite (toℕ t') i j) ≤⟨
                     max-inc (λ x → (toℕ x) + proj₁ (finite (toℕ x) i j)) t'
                     ⟩
                   expiryᵢⱼ t i j ≤⟨ expiryᵢⱼ≤expiryᵢ t i j ⟩
                   expiryᵢ t i   ≤⟨ expiryᵢ≤expiry t i ⟩
                   expiry t     ≤⟨ expiryₜ≤k ⟩
                   k ∎)))

  expiry-monotone : ∀ {t k} → t ≤ k → expiry t ≤ expiry k
  expiry-monotone t≤k = max-mono (λ i → expiryᵢ-monotone i t≤k)

  -- Properties of φ
  φ≤expiry-nextActive-φ : ∀ t i → φ t ≤ expiry (nextActive (φ t) i )
  φ≤expiry-nextActive-φ t i = begin
    φ t        ≤⟨ nextActive-inc (φ t) i ⟩
    nextActive (φ t) i  ≤⟨ expiry-inc (nextActive (φ t) i) ⟩
    expiry (nextActive (φ t) i)
    ∎

  φ-inc : ∀ t → t ≤ φ t
  φ-inc zero = z≤n
  φ-inc (suc t) = s≤s (begin
        t ≤⟨ φ-inc t ⟩
        φ t ≤⟨ max≤ (nextActive-inc (φ t)) ⟩
        max (nextActive (φ t)) ≤⟨ expiry-inc (max (nextActive (φ t))) ⟩
        expiry (max (nextActive (φ t))) ∎)
  
  φ<φs : ∀ t → φ t < φ (suc t)
  φ<φs t = s≤s (begin
       φ t ≤⟨ max≤ (nextActive-inc (φ t)) ⟩
       max (nextActive (φ t)) ≤⟨ expiry-inc (max (nextActive (φ t))) ⟩
       expiry (max (nextActive (φ t))) ∎)

  nextActiveφ<φs : ∀ t i → nextActive (φ t) i < φ (suc t)
  nextActiveφ<φs t i = s≤s (begin
      nextActive (φ t) i        ≤⟨ max-inc (nextActive (φ t)) i ⟩
      max (nextActive (φ t)) ≤⟨ expiry-inc (max (nextActive (φ t))) ⟩
      expiry (max (nextActive (φ t))) ∎
      )

  -- Propeties of τ
  φ≤τ : ∀ t i → φ t ≤ τ t i
  φ≤τ t i = nextActive-inc (φ t) i
  τ-inc : ∀ t i → t ≤ τ t i
  τ-inc t i = ≤-trans (φ-inc t) (nextActive-inc (φ t) i)

  prop1-i : φ zero ≡ zero
  prop1-i = refl

  prop1-ii : ∀ t i → ∃ λ k → (i ∈ α k) × (φ t ≤ k) × (k < φ (suc t))
  prop1-ii t i = nextActive (φ t) i ,
                 nextActive-active (φ t) i ,
                 nextActive-inc (φ t) i ,
                 nextActiveφ<φs t i

  prop1-iii : ∀ t i j k  → (φ t ≤ τ t j) × (τ t j ≤ β (φ (suc t) + k) i j)
  prop1-iii t i j k = φ≤τ t j , (begin
                nextActive (φ t) j ≤⟨ expiryₜ≤k⇒t≤βk
                  (nextActive (φ t) j) (φ (suc t) + k) i j
                  (begin
                    expiry (nextActive (φ t) j) ≤⟨
                      expiry-monotone (max-inc (nextActive (φ t)) j)
                      ⟩
                    expiry (max (nextActive (φ t)))  ≤⟨
                      n≤1+n (expiry (max (nextActive (φ t))))
                      ⟩
                    φ (suc t) ≤⟨ m≤m+n (φ (suc t)) k ⟩
                    φ (suc t) + k ∎)
                  ⟩
                β (φ (suc t) + k) i j ∎)
