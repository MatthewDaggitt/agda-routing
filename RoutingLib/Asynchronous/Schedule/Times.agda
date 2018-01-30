open import Level using () renaming (zero to lzero)
open import Data.Nat using (ℕ; zero; suc; s≤s; _<_; _≤_; _∸_; _≟_; _⊔_; _+_)
open import Data.Nat.Properties using (1+n≰n; ≤-refl; ≤+≢⇒<; <⇒≤; +-suc; +-identityʳ)
open import Data.Fin using (Fin; toℕ)
open import Data.Fin.Properties using ()
open import Data.Fin.Subset using (Subset; _∈_; ⊤)
open import Data.Fin.Dec using (_∈?_)
open import Data.Fin.Subset.Properties using (∈⊤)
open import Data.List using (foldr; tabulate; applyDownFrom)
open import Data.Product using (∃; _×_; _,_; proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; subst; cong)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Induction.WellFounded using (Acc; acc)
open import Induction.Nat using () renaming (<-well-founded to <-wf)

open import RoutingLib.Asynchronous.Schedule using (Schedule; 𝕋)
open import RoutingLib.Data.Nat.Properties using (m<n≤o⇒o∸n<o∸m)
open import RoutingLib.Data.Table using (max)

module RoutingLib.Asynchronous.Schedule.Times {n}(𝕤 : Schedule n) where

    open Schedule 𝕤

    ∈-α-comm : ∀ t k i → i ∈ α (t + suc k) → i ∈ α (suc t + k)
    ∈-α-comm t k i p = subst (i ∈_) (cong α (+-suc t k)) p

    -----------------
    -- Activations --
    -----------------

    -- nextActive' returns t+k given that i is accessed at time t+k
    nextActive' : (t k : 𝕋)(i : Fin n) → i ∈ α (t + suc k)
                  → Acc _<_ k → ∃ λ x → i ∈ α x
    nextActive' t zero    i p  _       = suc t ,
                subst (i ∈_) (cong α (trans (+-suc t 0) (cong suc (+-identityʳ t)))) p
    nextActive' t (suc k) i p (acc rs) with i ∈? α t
    ... | yes i∈α = t , i∈α
    ... | no  i∉α = nextActive' (suc t) k i (∈-α-comm t (suc k) i p)
        (rs k ≤-refl)

    -- nextActive returns a time after t, t', such that i is accessed at t'
    nextActive : 𝕋 → Fin n → 𝕋
    nextActive t i with (nonstarvation t i)
    ... | (k , p) = proj₁ (nextActive' t k i p (<-wf k))


    ---------------
    -- Data flow --
    ---------------

    -- expiryᵢⱼ returns a time such that i only uses data from j after time t
    expiryᵢⱼ : 𝕋 → Fin n → Fin n → 𝕋
    expiryᵢⱼ t i j = max {suc t} t (λ x → proj₁ (finite (toℕ x) i j))

    -- expiryᵢ returns a time ≥ t such that i only ever uses data from after time t
    expiryᵢ : 𝕋 → Fin n → 𝕋
    expiryᵢ t i = max t (expiryᵢⱼ t i)

    -- expiry returns a time ≥ t such that all nodes only ever uses data from after time t
    expiry : 𝕋 → 𝕋
    expiry t = max t (expiryᵢ t)

    
    ---------------
    -- Pseudo-Cycles --
    ---------------
    
    -- Definition of φ
    ϕ : ℕ → 𝕋
    ϕ zero    = zero
    ϕ (suc K) = suc (expiry (max {n} (ϕ K) (nextActive (ϕ K))))
    
    -- Definition of τ
    τ : ℕ → Fin n → 𝕋
    τ K i = nextActive (ϕ K) i



{-
    module ScheduleTimes (𝕤 : Schedule n) where
      
      open Schedule 𝕤
      open ActivationTimes nonstarvation
      open DataFlowTimes finite

      -- Time at which n complete "synchronous" iterations have occurred
      syncIter : ℕ → 𝕋
      syncIter zero    = zero
      syncIter (suc n) = nextTotalActivation (expiry (syncIter n))

      -- An abstract version of syncIter that can be used to increase performance
      abstract

        syncIter𝔸 : ℕ → 𝕋
        syncIter𝔸 = syncIter

        syncIter𝔸-equiv : syncIter𝔸 ≡ syncIter
        syncIter𝔸-equiv = refl



      -- pseudoperiodᵢ

      pseudoperiodᵢ : 𝕋 → Fin n → 𝕋
      pseudoperiodᵢ t i = nextActivation (expiryᵢ t i) i      

      -- pseudoperiod

      pseudoperiod : ℕ → 𝕋
      pseudoperiod zero = zero
      pseudoperiod (suc n) = foldr _⊔_ (suc (pseudoperiod n)) (tabulate (pseudoperiodᵢ (pseudoperiod n)))

      -- An abstract version of pseudoperiod that can be used to increase performance
      abstract

        pseudoperiod𝔸 : ℕ → 𝕋
        pseudoperiod𝔸 = pseudoperiod

        pseudoperiod𝔸-≡ : pseudoperiod𝔸 ≡ pseudoperiod
        pseudoperiod𝔸-≡ = refl

    open DataFlowTimes public
    open ActivationTimes public
    open ScheduleTimes public
-}
