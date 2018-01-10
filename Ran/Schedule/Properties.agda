-- imports
open import Schedule
  using (𝕋; Schedule)
open import Data.Nat
  using (ℕ; zero; suc; _<_; _+_; _≤_; s≤s; z≤n; _≟_; _>_; pred; _∸_; _≤?_)
open import Data.Fin.Subset
  using (Subset; _∈_)
open import Data.Product
  using (_,_; ∃; _×_; proj₁; proj₂)
open import Induction.WellFounded
  using (Acc; acc)
open import Data.Nat.Properties
  using (+-identityʳ; m≤m+n; ≤-trans; ≤-reflexive; +-suc; n≤1+n; m+n∸m≡n;
        <-trans; ≤+≢⇒<; pred-mono; ≤-antisym; +-mono-≤; <⇒≤; +-comm)
open import Relation.Binary.PropositionalEquality
  using (subst₂; cong; refl; _≡_; trans; sym; _≢_; cong₂; subst)
open import Induction.Nat
  using (<-well-founded)
open import Data.Fin
  using (Fin; toℕ; fromℕ; inject₁) renaming (zero to fzero; suc to fsuc)
open import Functions
  using (max)
open import Functions.Properties
  using(max-inc=n; max<; max≤; max-inc)
open import Data.Fin.Dec
  using (_∈?_)
open import Relation.Nullary
  using (yes; no)
open import Function
  using (_∘_)
open import Data.Fin.Properties
  using (prop-toℕ-≤; inject₁-lemma; to-from)
open import Relation.Nullary.Product
  using (_×-dec_)
open import Relation.Nullary.Negation
  using (contradiction)
open import Data.Fin.Subset.Properties
  using (∈⊤)

open Data.Nat.Properties.≤-Reasoning
  using (_≤⟨_⟩_; begin_; _∎)
    
module Schedule.Properties {n : ℕ}(s : Schedule n) where
  open Schedule.Schedule s
  open Schedule.Timing s

  -- general property
  ∀≢⇒< : (t k : 𝕋) → (∀ (t' : Fin (suc t)) → k ≢ (toℕ t')) → t < k
  ∀≢⇒< zero k p = ≤+≢⇒< z≤n ((p fzero) ∘ sym)
  ∀≢⇒< (suc t) k p = ≤+≢⇒<
       (∀≢⇒< t k (λ t' → subst (k ≢_) (inject₁-lemma t') (p (inject₁ t'))))
       (subst (k ≢_) (to-from (suc t)) (p (fromℕ (suc t))) ∘ sym)

  -- Properties of finite
  finite-inc : ∀ t i → t ≤ t + proj₁ (finite t i)
  finite-inc t i = m≤m+n t (proj₁ (finite t i))
  
  finite-fin : ∀ t k i → (t' : Fin (suc t)) →
              (toℕ t') + proj₁ (finite (toℕ t') i) ≤ k → β k i ≢ toℕ t'
  finite-fin t k i t' p  with finite (toℕ t') i
  ... | (m , q) = subst (_≢ toℕ t')
        (cong (λ x → β x i) (m+n∸m≡n p))
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


  -- Properties of expiry
  expiry-inc : ∀ t i → t ≤ expiry t i
  expiry-inc t i = max-inc=n
        (λ x → (toℕ x) + proj₁ (finite (toℕ x) i))
        (λ j → finite-inc (toℕ j) i)

  expiryₜ≤k⇒t≤βk : ∀ t k i → expiry t i ≤ k → t ≤ β k i
  expiryₜ≤k⇒t≤βk t k i p = <⇒≤
            (∀≢⇒< t (β k i)
            (λ t' →  finite-fin t k i t'
            (≤-trans
              (max-inc (λ x → (toℕ x) + proj₁ (finite (toℕ x) i)) t')
              p)
            ))

  -- Properties of φ
  φ≤expiry-nextActive-φ : ∀ t i → φ t ≤ expiry (nextActive (φ t) i ) i
  φ≤expiry-nextActive-φ t i = begin
    φ t        ≤⟨ nextActive-inc (φ t) i ⟩
    nextActive (φ t) i  ≤⟨ expiry-inc (nextActive (φ t) i) i ⟩
    expiry (nextActive (φ t) i) i
    ∎

  φ-inc : ∀ t → t ≤ φ t
  φ-inc zero = z≤n
  φ-inc (suc t) = s≤s (max≤ {f = (λ i → expiry (nextActive (φ t) i) i)}
        (λ i → ≤-trans (φ-inc t) (φ≤expiry-nextActive-φ t i)))

  φ<φs : ∀ t → φ t < φ (suc t)
  φ<φs t = s≤s (max≤ (φ≤expiry-nextActive-φ t))

  nextActiveφ<φs : ∀ t i → nextActive (φ t) i < φ (suc t)
  nextActiveφ<φs t i = s≤s (
    begin nextActive (φ t) i        ≤⟨ expiry-inc (nextActive (φ t) i) i ⟩
      expiry (nextActive (φ t) i) i  ≤⟨ max-inc (λ j → expiry (nextActive (φ t) j) j) i ⟩
      max (λ j → expiry (nextActive (φ t) j) j)
      ∎
    )

  -- Propeties of τ
  φ≤τ : ∀ t i → φ t ≤ τ t i
  φ≤τ t i = nextActive-inc (φ t) i

  τ-inc : ∀ t i → t ≤ τ t i
  τ-inc t i = ≤-trans (φ-inc t) (nextActive-inc (φ t) i)

  -- Proposition 1
  prop1-i : φ zero ≡ zero
  prop1-i = refl

  prop1-ii : ∀ t i → ∃ λ k → (i ∈ α k) × (φ t ≤ k) × (k < φ (suc t))
  prop1-ii t i = nextActive (φ t) i ,
                 nextActive-active (φ t) i ,
                 nextActive-inc (φ t) i ,
                 nextActiveφ<φs t i

  prop1-iii : ∀ t i k  → (φ t ≤ τ t i) × (τ t i ≤ β (φ (suc t) + k) i)
  prop1-iii t i k = φ≤τ t i , (begin
                τ t i      ≤⟨ ≤-reflexive refl ⟩
                nextActive (φ t) i  ≤⟨
                  expiryₜ≤k⇒t≤βk (nextActive (φ t) i) (φ (suc t) + k) i
                  (begin
                    expiry (nextActive (φ t) i) i  ≤⟨ max-inc (λ j → expiry (nextActive (φ t) j) j) i ⟩
                    max (λ j → expiry (nextActive (φ t) j) j)
                                     ≤⟨ n≤1+n (max (λ j → expiry (nextActive (φ t) j) j)) ⟩
                    φ (suc t)        ≤⟨ m≤m+n (φ (suc t)) k ⟩
                    φ (suc t) + k ∎)
                ⟩
                β (φ (suc t) + k) i
                ∎ )
