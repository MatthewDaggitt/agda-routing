open import Data.Nat using (ℕ; zero; suc; _≤_; _<_; _⊔_; _∸_; _+_; z≤n; s≤s; _≟_; _≤?_; ≤-pred)
open import Data.Nat.Properties using (m≤m⊔n; n≤1+n; ⊔-sel; module ≤-Reasoning; <-cmp; ≤+≢⇒<; ≤-refl; <⇒≤; ⊔-identityʳ; <-irrefl; ≤-trans; ≤-reflexive; ≮⇒≥; n≤m⊔n; ⊔-mono-≤; m≤m+n; m+n∸m≡n)
open import Data.Fin using (Fin; toℕ; fromℕ; inject≤) renaming (zero to fzero)
open import Data.Fin.Properties using (inject≤-lemma)
open import Data.Fin.Subset using (_∈_)
open import Data.Fin.Subset.Properties using (∈⊤)
open import Data.Fin.Dec using (_∈?_)
open import Data.Product using (∃; _,_; _×_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂; _⊎_)
open import Data.List using (List; []; _∷_; foldr; map; allFin; applyDownFrom; tabulate)
open import Data.List.Any using (Any) renaming (map to anyMap)
open import Data.List.Any.Properties using (map⁺)
open import Data.List.Any.Membership.Propositional.Properties using (∈-map⁺)
open import Data.Vec using (Vec; lookup) renaming (map to mapᵥ; allFin to allFinᵥ)
open import Induction.WellFounded using (Acc; acc)
open import Induction.Nat using () renaming (<-well-founded to <-wf)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary using (tri<; tri≈; tri>)
open import Relation.Binary.PropositionalEquality using (refl; sym; trans; cong; subst; _≢_; _≡_)

open import RoutingLib.Asynchronous.Schedule
open import RoutingLib.Data.Nat.Properties using ( m<n≤o⇒o∸n<o∸m; m≤n⊎m≤o⇒m≤n⊔o; ∀x≤m:n≢x⇒m<n; m⊔n≡m⇒n≤m; n⊔m≡m⇒n≤m)
open import RoutingLib.Data.Table using (max)
open import RoutingLib.Data.Table.Properties using (t≤max[t]; x≤max[t]; max[t]≤max[s]; max[t]≤max[s]₂; ⊥≤max[t])
open import RoutingLib.Data.List.Any.Membership.Propositional using (∈-allFin⁺; ∈-tabulate⁺; ∈-applyDownFrom⁺)
import RoutingLib.Asynchronous.Schedule.Times as Times

module RoutingLib.Asynchronous.Schedule.Times.Properties {n} (𝕤 : Schedule n) where

  open Schedule 𝕤
  open Times 𝕤
  
  -----------------
  -- Finite --
  -----------------
  finite-inc : ∀ t i j → t ≤ t + proj₁ (finite t i j)
  finite-inc t i j = m≤m+n t (proj₁ (finite t i j))

  finite-fin : ∀ t k i j → (t' : Fin (suc t)) →
              (toℕ t') + proj₁ (finite (toℕ t') i j) ≤ k →
              β k i j ≢ toℕ t'
  finite-fin t k i j t' p  with finite (toℕ t') i j
  ... | (m , q) = subst (_≢ toℕ t')
        (cong (λ x → β x i j) (m+n∸m≡n p))
        (q (k ∸ (toℕ t' + m)))

  -----------------
  -- Activations --
  -----------------
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
  ... | k , p = nextActive'-inc (suc t) k i p (<-wf k)

  nextActive-active : ∀ t i → i ∈ α (nextActive t i)
  nextActive-active zero i = subst (i ∈_) (sym α₀) ∈⊤
  nextActive-active (suc t) i with nonstarvation (suc t) i
  ... | k , p with nextActive' (suc t) k i p (<-wf k)
  ... | _ , active = active

  ---------------
  -- Data flow --
  ---------------
  -- Properties of expiryᵢⱼ
  postulate expiryᵢⱼ-inc : ∀ t i j → t ≤ expiryᵢⱼ t i j
  --expiryᵢⱼ-inc t i j = ≤-trans (finite-inc t i j) (≤-trans {!!} (t≤max[t] {suc t} zero (λ x → (toℕ x) + proj₁ (finite (toℕ x) i j)) (fromℕ t) ))
              -- (λ x → (toℕ x) + proj₁ (finite (toℕ x) i j))
              -- (λ x → finite-inc (toℕ x) i j)

  expiryᵢⱼ-monotone : ∀ {t k} → t ≤ k → ∀ i j → expiryᵢⱼ t i j ≤ expiryᵢⱼ k i j
  expiryᵢⱼ-monotone {t} {k} t≤k i j = max[t]≤max[s]₂ {suc t} {suc k}
                    (s≤s t≤k) z≤n
                    {λ x → (toℕ x) + proj₁ (finite (toℕ x) i j)}
                    {λ x → (toℕ x) + proj₁ (finite (toℕ x) i j)}
                    ( λ x → ≤-reflexive (trans
                      (cong (_+ proj₁ (finite (toℕ x) i j))
                        (sym (inject≤-lemma x (s≤s t≤k))))
                      (cong (toℕ (inject≤ x (s≤s t≤k)) +_)
                        (cong (λ y → proj₁ (finite y i j))
                          (sym (inject≤-lemma x (s≤s t≤k)))))))


  -- Properties of expiryᵢ
  expiryᵢⱼ≤expiryᵢ : ∀ t i j → expiryᵢⱼ t i j ≤ expiryᵢ t i
  expiryᵢⱼ≤expiryᵢ t i j = t≤max[t] t (expiryᵢⱼ t i) j

  expiryᵢ-inc : ∀ t i → t ≤ expiryᵢ t i
  expiryᵢ-inc t i = ⊥≤max[t] t (expiryᵢⱼ t i)

  expiryᵢ-monotone : ∀ {t k} i → t ≤ k → expiryᵢ t i ≤ expiryᵢ k i
  expiryᵢ-monotone {t} {k} i t≤k = max[t]≤max[s] t k t≤k (expiryᵢⱼ-monotone t≤k i)

  -- Properties of expiry
  expiryᵢ≤expiry : ∀ t i → expiryᵢ t i ≤ expiry t 
  expiryᵢ≤expiry t i = t≤max[t] t (expiryᵢ t) i

  expiry-inc : ∀ t → t ≤ expiry t
  expiry-inc t = ⊥≤max[t] t (expiryᵢ t)

  postulate expiryₜ≤k⇒t≤βk : ∀ t k i j → expiry t ≤ k → t ≤ β k i j
  -- expiryₜ≤k⇒t≤βk t k i j expiryₜ≤k = <⇒≤ (∀x≤m:n≢x⇒m<n t (β k i j) λ x≤t → {!!})


{-(∀≢⇒< t (β k i j)
                 (λ t' → finite-fin t k i j t' (begin
                   (toℕ t') + proj₁ (finite (toℕ t') i j) ≤⟨
                     max-inc (λ x → (toℕ x) + proj₁ (finite (toℕ x) i j)) t'
                     ⟩
                   expiryᵢⱼ t i j ≤⟨ expiryᵢⱼ≤expiryᵢ t i j ⟩
                   expiryᵢ t i   ≤⟨ expiryᵢ≤expiry t i ⟩
                   expiry t     ≤⟨ expiryₜ≤k ⟩
                   k ∎)))-}

  expiry-monotone : ∀ {t k} → t ≤ k → expiry t ≤ expiry k
  expiry-monotone {t} {k} t≤k = max[t]≤max[s] t k t≤k (λ i → expiryᵢ-monotone i t≤k)

   ---------------
  -- Psuedo-cycles --
  ---------------

  open ≤-Reasoning
  
  -- Properties of φ
  φ≤expiry-nextActive-φ : ∀ t i → φ t ≤ expiry (nextActive (φ t) i )
  φ≤expiry-nextActive-φ t i = begin
    φ t                         ≤⟨ nextActive-inc (φ t) i ⟩
    nextActive (φ t) i          ≤⟨ expiry-inc (nextActive (φ t) i) ⟩
    expiry (nextActive (φ t) i) ∎
   

  
  φ<φs : ∀ t → φ t < φ (suc t)
  φ<φs t = s≤s (begin
       φ t                                   ≤⟨ ⊥≤max[t] (φ t) (nextActive (φ t)) ⟩ 
       max (φ t) (nextActive (φ t))          ≤⟨ expiry-inc (max (φ t) (nextActive (φ t))) ⟩
       expiry (max (φ t) (nextActive (φ t))) ∎)
       
  φ-inc : ∀ t → t ≤ φ t
  φ-inc zero = z≤n
  φ-inc (suc t) = s≤s (begin
        t                                     ≤⟨ φ-inc t ⟩
        φ t                                   ≤⟨ ⊥≤max[t] (φ t) (nextActive (φ t)) ⟩
        max (φ t) (nextActive (φ t))          ≤⟨ expiry-inc (max (φ t) (nextActive (φ t))) ⟩
        expiry (max (φ t) (nextActive (φ t))) ∎)

  nextActiveφ<φs : ∀ t i → nextActive (φ t) i < φ (suc t)
  nextActiveφ<φs t i = s≤s (begin
      nextActive (φ t) i              ≤⟨ t≤max[t] (φ t) (nextActive (φ t)) i ⟩
      max (φ t) (nextActive (φ t))          ≤⟨ expiry-inc (max (φ t) (nextActive (φ t))) ⟩
      expiry (max (φ t) (nextActive (φ t))) ∎
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
  prop1-iii t i j k = φ≤τ t j , (expiryₜ≤k⇒t≤βk
    (nextActive (φ t) j) (φ (suc t) + k) i j
    (begin
       expiry (nextActive (φ t) j)      ≤⟨ expiry-monotone (t≤max[t] (φ t) (nextActive (φ t)) j) ⟩
       expiry (max (φ t) (nextActive (φ t)))  ≤⟨ n≤1+n (expiry (max (φ t) (nextActive (φ t)))) ⟩
       φ (suc t)                        ≤⟨ m≤m+n (φ (suc t)) k ⟩
       φ (suc t) + k                    ∎))
                
