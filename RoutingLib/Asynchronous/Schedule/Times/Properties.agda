open import Data.Nat using (ℕ; zero; suc; _≤_; _<_; _⊔_; _∸_; _+_; z≤n; s≤s; _≟_; _≤?_; ≤-pred)
open import Data.Nat.Properties using (m≤m⊔n; n≤1+n; ⊔-sel; module ≤-Reasoning; <-cmp; ≤+≢⇒<; ≤-refl; <⇒≤; ⊔-identityʳ; <-irrefl; ≤-trans; ≤-reflexive; ≮⇒≥; n≤m⊔n; ⊔-mono-≤; m≤m+n; m+n∸m≡n; <⇒≢)
open import Data.Fin using (Fin; toℕ; fromℕ; inject≤; inject₁) renaming (zero to fzero)
open import Data.Fin.Properties using (inject≤-lemma; to-from; inject₁-lemma)
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
open import Function using (_∘_)
open import Induction.WellFounded using (Acc; acc)
open import Induction.Nat using () renaming (<-well-founded to <-wf)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary using (tri<; tri≈; tri>)
open import Relation.Binary.PropositionalEquality using (refl; sym; trans; cong; subst; _≢_; _≡_)

open import RoutingLib.Asynchronous.Schedule
open import RoutingLib.Data.Nat.Properties using ( m<n≤o⇒o∸n<o∸m; m≤n⊎m≤o⇒m≤n⊔o; ∀x≤m:n≢x⇒m<n; m⊔n≡m⇒n≤m; n⊔m≡m⇒n≤m)
open import RoutingLib.Data.Table using (max)
open import RoutingLib.Data.Table.Properties using (t≤max[t]; x≤max[t]; max[s]≤max[t]; ⊥≤max[t])
import RoutingLib.Asynchronous.Schedule.Times as Times

module RoutingLib.Asynchronous.Schedule.Times.Properties {n} (𝕤 : Schedule n) where

  open Schedule 𝕤
  open Times 𝕤

  -----------------
  -- Finite --
  -----------------
  finite-fin : ∀ {t} k i j (t' : Fin (suc t)) →
              proj₁ (finite (toℕ t') i j) ≤ k →
              β k i j ≢ toℕ t'
  finite-fin {t} k i j t' p  with finite (toℕ t') i j
  ... | (m , q) = subst (_≢ toℕ t')
    (cong (λ x → β x i j) (m+n∸m≡n p))
    (q (k ∸ m)) 

  -----------------
  -- Activations --
  -----------------
  -- Properties of nextActive'
  nextActive'-inc : ∀ t k i (p : i ∈ α (t + suc k))(accₖ : Acc _<_ k) →
                    t ≤ proj₁ (nextActive' t k i p accₖ)
  nextActive'-inc t zero i p _ = n≤1+n t
  nextActive'-inc t (suc k) i p (acc rs) with i ∈? α t
  ... | yes i∈α = ≤-reflexive refl
  ... | no  i∉α = ≤-trans (n≤1+n t)
                  (nextActive'-inc (suc t) k i (∈-α-comm t (suc k) i p)
                    (rs k (≤-reflexive refl)))

  -- Properties of nextActive
  nextActive-inc : ∀ t i → t ≤ nextActive t i
  nextActive-inc t i with nonstarvation t i
  ... | k , p = nextActive'-inc t k i p (<-wf k)

  nextActive-active : ∀ t i → i ∈ α (nextActive t i)
  nextActive-active t i with nonstarvation t i
  ... | (k , p) = proj₂ (nextActive' t k i p (<-wf k))

  ---------------
  -- Data flow --
  ---------------
  -- Properties of expiryᵢⱼ
  expiryᵢⱼ-inc : ∀ t i j → t ≤ expiryᵢⱼ t i j
  expiryᵢⱼ-inc t i j = ⊥≤max[t] {suc t} t ((λ x → proj₁ (finite (toℕ x) i j)))

  expiryᵢⱼ-monotone : ∀ {t k} → t ≤ k → ∀ i j → expiryᵢⱼ t i j ≤ expiryᵢⱼ k i j
  expiryᵢⱼ-monotone {t} {k} t≤k i j = max[s]≤max[t] t {k} {suc t} {suc k}
                    {(λ x → proj₁ (finite (toℕ x) i j))}
                    {(λ x → proj₁ (finite (toℕ x) i j))}
                    (inj₁ t≤k) λ x → inj₂ (inject≤ x (s≤s t≤k) , ≤-reflexive (inject-x x))
                    where
                    inject-x : ∀ x → proj₁ (finite (toℕ x) i j) ≡
                               proj₁ (finite (toℕ (inject≤ x (s≤s t≤k))) i j)
                    inject-x x = cong (λ y → proj₁ (finite y i j))
                      (sym (inject≤-lemma x (s≤s t≤k)))


  expiryᵢⱼt≤k⇒t≤βk : ∀ {t k i j} → expiryᵢⱼ t i j ≤ k → t ≤ β k i j
  expiryᵢⱼt≤k⇒t≤βk {t} {k} {i} {j} expiryᵢⱼt≤k = <⇒≤ (∀x≤m:n≢x⇒m<n t (β k i j)
                   (λ {x} x≤t → subst (β k i j ≢_) (x'≡x x x≤t) (β≢t' (x' x x≤t))))
                   where
                   x' : ∀ x x≤t → Fin (suc t)
                   x' x x≤t = inject≤ (fromℕ x) (s≤s x≤t)
                   x'≡x : ∀ x x≤t → toℕ (x' x x≤t) ≡ x
                   x'≡x x x≤t = trans (inject≤-lemma (fromℕ x) (s≤s x≤t)) (to-from x)
                   finite[t']≤expiry : ∀ (t' : Fin (suc t)) →
                               proj₁ (finite (toℕ t') i j) ≤ expiryᵢⱼ t i j
                   finite[t']≤expiry t' = t≤max[t] t (λ x → proj₁ (finite (toℕ x) i j)) t'
                   β≢t' : ∀ (t' : Fin (suc t)) → β k i j ≢ toℕ t'
                   β≢t' t' = finite-fin k i j t' (≤-trans (finite[t']≤expiry t') expiryᵢⱼt≤k)

  -- Properties of expiryᵢ
  expiryᵢⱼ≤expiryᵢ : ∀ t i j → expiryᵢⱼ t i j ≤ expiryᵢ t i
  expiryᵢⱼ≤expiryᵢ t i j = t≤max[t] t (expiryᵢⱼ t i) j

  expiryᵢ-inc : ∀ t i → t ≤ expiryᵢ t i
  expiryᵢ-inc t i = ⊥≤max[t] t (expiryᵢⱼ t i)

  expiryᵢ-monotone : ∀ {t k} → t ≤ k → ∀ i → expiryᵢ t i ≤ expiryᵢ k i
  expiryᵢ-monotone {t} {k} t≤k i = max[s]≤max[t] t (inj₁ t≤k)
                   (λ j → inj₂ (j , expiryᵢⱼ-monotone t≤k i j))

  expiryᵢt≤k⇒t≤βk : ∀ {t k i} → expiryᵢ t i ≤ k → ∀ j → t ≤ β k i j
  expiryᵢt≤k⇒t≤βk {t} {k} {i} expiryᵢt≤k j = expiryᵢⱼt≤k⇒t≤βk
                  (≤-trans (expiryᵢⱼ≤expiryᵢ t i j) expiryᵢt≤k)

  -- Properties of expiry
  expiryᵢ≤expiry : ∀ t i → expiryᵢ t i ≤ expiry t 
  expiryᵢ≤expiry t i = t≤max[t] t (expiryᵢ t) i

  expiry-inc : ∀ t → t ≤ expiry t
  expiry-inc t = ⊥≤max[t] t (expiryᵢ t)

  expiryₜ≤k⇒t≤βk : ∀ {t k} → expiry t ≤ k → ∀ i j → t ≤ β k i j
  expiryₜ≤k⇒t≤βk {t} {k} expiryₜ≤k i j = expiryᵢt≤k⇒t≤βk
    (≤-trans (expiryᵢ≤expiry t i) expiryₜ≤k) j

  expiry-monotone : ∀ {t k} → t ≤ k → expiry t ≤ expiry k
  expiry-monotone {t} {k} t≤k = max[s]≤max[t] t {k} (inj₁ t≤k) (λ i → inj₂ (i , expiryᵢ-monotone t≤k i))

   ---------------
  -- Psuedo-cycles --
  ---------------

  open ≤-Reasoning
  
  -- Properties of ϕ
  ϕ≤expiry-nextActive-ϕ : ∀ K i → ϕ K ≤ expiry (nextActive (ϕ K) i )
  ϕ≤expiry-nextActive-ϕ K i = begin
    ϕ K                         ≤⟨ nextActive-inc (ϕ K) i ⟩
    nextActive (ϕ K) i          ≤⟨ expiry-inc (nextActive (ϕ K) i) ⟩
    expiry (nextActive (ϕ K) i) ∎
   

  
  ϕ<ϕs : ∀ K → ϕ K < ϕ (suc K)
  ϕ<ϕs K = s≤s (begin
       ϕ K                                   ≤⟨ ⊥≤max[t] (ϕ K) (nextActive (ϕ K)) ⟩ 
       max (ϕ K) (nextActive (ϕ K))          ≤⟨ expiry-inc (max (ϕ K) (nextActive (ϕ K))) ⟩
       expiry (max (ϕ K) (nextActive (ϕ K))) ∎)
       
  ϕ-inc : ∀ K → K ≤ ϕ K
  ϕ-inc zero = z≤n
  ϕ-inc (suc K) = s≤s (begin
        K                                     ≤⟨ ϕ-inc K ⟩
        ϕ K                                   ≤⟨ ⊥≤max[t] (ϕ K) (nextActive (ϕ K)) ⟩
        max (ϕ K) (nextActive (ϕ K))          ≤⟨ expiry-inc (max (ϕ K) (nextActive (ϕ K))) ⟩
        expiry (max (ϕ K) (nextActive (ϕ K))) ∎)

  nextActiveϕ<ϕs : ∀ K i → nextActive (ϕ K) i < ϕ (suc K)
  nextActiveϕ<ϕs K i = s≤s (begin
      nextActive (ϕ K) i                    ≤⟨ t≤max[t] (ϕ K) (nextActive (ϕ K)) i ⟩
      max (ϕ K) (nextActive (ϕ K))          ≤⟨ expiry-inc (max (ϕ K) (nextActive (ϕ K))) ⟩
      expiry (max (ϕ K) (nextActive (ϕ K))) ∎
      )

  -- Propeties of τ
  ϕ≤τ : ∀ K i → ϕ K ≤ τ K i
  ϕ≤τ zero     i = z≤n
  ϕ≤τ (suc K)  i = nextActive-inc (ϕ (suc K)) i
  
  τ-inc : ∀ K i → K ≤ τ K i
  τ-inc zero     i = z≤n
  τ-inc (suc K)  i = ≤-trans (ϕ-inc (suc K)) (nextActive-inc (ϕ (suc K)) i)

  ϕ₀≡0 : ϕ zero ≡ zero
  ϕ₀≡0 = refl

  active-in-ϕ : ∀ K i → ∃ λ t → (i ∈ α t) × (ϕ K ≤ t) × (t < ϕ (suc K))
  active-in-ϕ K i =  nextActive         (ϕ K)  i ,
                     nextActive-active  (ϕ K)  i ,
                     nextActive-inc     (ϕ K)  i ,
                     nextActiveϕ<ϕs     K      i

  ϕ≤τ≤βϕs+t : ∀ K i j t  → (ϕ K ≤ τ K j) × (τ K j ≤ β (ϕ (suc K) + t) i j)
  ϕ≤τ≤βϕs+t K i j t = ϕ≤τ K j , expiryₜ≤k⇒t≤βk expiry-nextϕⱼ≤ϕₛ+t i j
    where
    nextϕ : Fin n → 𝕋
    nextϕ = nextActive (ϕ K)

    expiry-nextϕⱼ≤ϕₛ+t : expiry (nextϕ j) ≤ ϕ (suc K) + t
    expiry-nextϕⱼ≤ϕₛ+t = begin
      expiry (nextϕ j)          ≤⟨ expiry-monotone (t≤max[t] (ϕ K) nextϕ j) ⟩
      expiry (max (ϕ K) nextϕ)  ≤⟨ n≤1+n (expiry (max (ϕ K) nextϕ)) ⟩
      ϕ (suc K)                 ≤⟨ m≤m+n (ϕ (suc K)) t ⟩
      ϕ (suc K) + t             ∎
