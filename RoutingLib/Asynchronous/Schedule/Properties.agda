open import Data.Nat using (ℕ; zero; suc; _≤_; _<_; _⊔_; _∸_; z≤n; s≤s; _≟_; _≤?_; module ≤-Reasoning)
open import Data.Nat.Properties using (m≤m⊔n; n≤1+n; ⊔-sel)
open import Data.Fin using (Fin; toℕ)
open import Data.Fin.Properties using ()
open import Data.Fin.Subset using (_∈_)
open import Data.Fin.Dec using (_∈?_)
open import Data.Product using (∃; _,_; _×_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂; _⊎_)
open import Data.List.Any using (Any) renaming (map to anyMap)
open import Data.List using (List; foldr; map; []; _∷_)
open import Data.Vec using (Vec; lookup) renaming (map to mapᵥ; allFin to allFinᵥ)
open import Induction.WellFounded using (Acc; acc)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary using (tri<; tri≈; tri>)
open import Relation.Binary.PropositionalEquality using (refl; sym; cong; subst; _≢_; _≡_)

open import RoutingLib.Asynchronous.Schedule using (Schedule; module SpecialTimes)
open import RoutingLib.Data.Nat.Properties using (cmp; ≤+≢⇒<; m<n≤o⇨o∸n<o∸m; ≤-refl; <⇒≤; ⊔-⊎preserves-x≤; ∀x≤m:n≢x⇒m<n; 0-idᵣ-⊔; <-irrefl; ≤-trans; ≤-reflexive; ≮⇒≥; m⊔n≡m⇨n≤m; n⊔m≡m⇨n≤m; n≤m⊔n; m+1≤n+1⇨m≤n)
open import RoutingLib.Induction.Nat using () renaming (<-well-founded to <-wf)
open import RoutingLib.Data.List using (allFin; applyDownFrom; tabulate)
open import RoutingLib.Data.List.Folds using (foldr-⊎preserves)
open import RoutingLib.Data.List.Any.Properties using (map⁺)
open import RoutingLib.Data.List.Any.PropositionalMembership using (∈-allFin; ∈-map; ∈-tabulate)

module RoutingLib.Asynchronous.Schedule.Properties {p : ℕ} (sch : Schedule p) where

  open Schedule sch
  open SpecialTimes sch
  
  -----------------
  -- Activations --
  -----------------

  abstract

    -- nextActivation

    private

      nextActivation-after' : ∀ {t t' i} tAcc → (t<t' : t < t') → (i∈αₜ' : i ∈ α t') → t < nextActivation' tAcc t<t' i∈αₜ'
      nextActivation-after' {t} {t'} {i} (acc t'∸t-acc) t<t' i∈αₜ' with i ∈? α (suc t) | (suc t) ≟ t'
      ... | yes i∈αₜ₊₁ | _          = ≤-refl
      ... | no  i∉αₜ₊₁ | yes t+1≡t' = contradiction (subst (λ t → i ∈ α t) (sym t+1≡t') i∈αₜ') i∉αₜ₊₁
      ... | no  i∉αₜ₊₁ | no  t+1≢t' = <⇒≤ (nextActivation-after' (t'∸t-acc (t' ∸ suc t) (m<n≤o⇨o∸n<o∸m ≤-refl t<t')) (≤+≢⇒< t<t' t+1≢t') i∈αₜ')
    
      nextActivation-active' : ∀ {t t' i} tAcc → (t<t' : t < t') → (i∈αₜ' : i ∈ α t') → i ∈ α (nextActivation' tAcc t<t' i∈αₜ')
      nextActivation-active' {t} {t'} {i} (acc t'∸t-acc) t<t' i∈αₜ' with i ∈? α (suc t) | (suc t) ≟ t'
      ... | yes i∈αₜ₊₁ | _          = i∈αₜ₊₁
      ... | no  i∉αₜ₊₁ | yes t+1≡t' = contradiction (subst (λ t → i ∈ α t) (sym t+1≡t') i∈αₜ') i∉αₜ₊₁
      ... | no  i∉αₜ₊₁ | no  t+1≢t' = nextActivation-active' (t'∸t-acc (t' ∸ suc t) (m<n≤o⇨o∸n<o∸m ≤-refl t<t')) (≤+≢⇒< t<t' t+1≢t') i∈αₜ'

      nextActivation-next' : ∀ {t t' i} tAcc → (t<t' : t < t') → (i∈αₜ' : i ∈ α t') → (∀ {t''} → t < t'' → i ∈ α t'' → (nextActivation' tAcc t<t' i∈αₜ') ≤ t'')
      nextActivation-next' {t} {t'} {i} (acc t'∸t-acc) t<t' i∈αₜ' with i ∈? α (suc t) | (suc t) ≟ t'
      ... | yes i∈αₜ₊₁ | _          = λ t<t'' _ → t<t''
      ... | no  i∉αₜ₊₁ | yes t+1≡t' = contradiction (subst (λ t → i ∈ α t) (sym t+1≡t') i∈αₜ') i∉αₜ₊₁
      ... | no  i∉αₜ₊₁ | no  t+1≢t' with nextActivation-next' (t'∸t-acc (t' ∸ suc t) (m<n≤o⇨o∸n<o∸m ≤-refl t<t')) (≤+≢⇒< t<t' t+1≢t') i∈αₜ'
      ...   | earliest = λ t<t'' i∈αₜ'' → earliest (≤+≢⇒< t<t'' (λ t+1≡t'' → i∉αₜ₊₁ (subst (λ t → i ∈ α t) (sym t+1≡t'') i∈αₜ''))) i∈αₜ''

    nextActivation-after : ∀ t i → t < nextActivation t i
    nextActivation-after t i with infiniteActivation t i
    ... | (t' , t<t' , i∈αₜ') = nextActivation-after' (<-wf (t' ∸ t)) t<t' i∈αₜ'
  
    nextActivation-active : ∀ t i → i ∈ α (nextActivation t i)
    nextActivation-active t i with infiniteActivation t i
    ... | (t' , t<t' , i∈αₜ') = nextActivation-active' (<-wf (t' ∸ t)) t<t' i∈αₜ'

    nextActivation-next : ∀ {t i t''} → t < t'' → i ∈ α t'' → nextActivation t i ≤ t''
    nextActivation-next {t} {i} with infiniteActivation t i
    ... | (t' , t<t' , i∈αₜ') = nextActivation-next' (<-wf (t' ∸ t)) t<t' i∈αₜ'

    nextActivation-all : ∀ t i → ∃ λ tₐ → t < tₐ × i ∈ α tₐ × (∀ {t''} → t < t'' → i ∈ α t'' → tₐ ≤ t'')
    nextActivation-all t i = nextActivation t i , nextActivation-after t i , nextActivation-active t i , nextActivation-next


    --  nextTotalActivation

    nextTotalActivation-after : ∀ t → t < nextTotalActivation t
    nextTotalActivation-after t = foldr-⊎preserves (t <_) ⊔-⊎preserves-x≤ (suc t) (tabulate (nextActivation t)) (inj₁ ≤-refl)

    nextTotalActivation-activated : ∀ t i → ∃ λ t' → t < t' × t' ≤ nextTotalActivation t × i ∈ α t'
    nextTotalActivation-activated t i = nextActivation t i , nextActivation-after t i , foldr-⊎preserves (nextActivation t i ≤_) ⊔-⊎preserves-x≤ (suc t) (tabulate (nextActivation t)) (inj₂ (anyMap ≤-reflexive (∈-tabulate (nextActivation t) i))) , nextActivation-active t i


    -- previousActivation

    previousActivation-before : ∀ {t p i} (p≤t : p ≤ t) (i∈αₚ : i ∈ α p) → previousActivation p≤t i∈αₚ ≤ t
    previousActivation-before {t} {p} {i} _ _ with i ∈? α t | p ≟ t
    previousActivation-before {t}         p≤t _    | yes i∈αₜ | _        = ≤-refl
    previousActivation-before {t}         p≤t i∈αₚ | no  _    | yes refl = p≤t
    previousActivation-before {t} {p} {i} p≤t i∈αₚ | no  i∉αₜ | no p≢t   with ≤+≢⇒< p≤t p≢t
    ... | s≤s p≤t₂ = ≤-trans (previousActivation-before p≤t₂ i∈αₚ) (n≤1+n _)

    previousActivation-after : ∀ {t p i} (p≤t : p ≤ t) (i∈αₚ : i ∈ α p) → p ≤ previousActivation p≤t i∈αₚ
    previousActivation-after {t} {p} {i} _ _ with i ∈? α t | p ≟ t
    previousActivation-after {t}         p≤t _    | yes i∈αₜ | _        = p≤t
    previousActivation-after {t}         p≤t i∈αₚ | no  _    | yes refl = p≤t
    previousActivation-after {t} {p} {i} p≤t i∈αₚ | no  i∉αₜ | no p≢t   with ≤+≢⇒< p≤t p≢t
    ... | s≤s p≤t₂ = previousActivation-after p≤t₂ i∈αₚ

    previousActivation-active : ∀ {t p i} (p≤t : p ≤ t) (i∈αₚ : i ∈ α p) → i ∈ α (previousActivation p≤t i∈αₚ)
    previousActivation-active {t} {p} {i} _ _ with i ∈? α t | p ≟ t
    previousActivation-active {t}         p≤t _    | yes i∈αₜ | _        =  i∈αₜ
    previousActivation-active {t}         p≤t i∈αₚ | no  _    | yes refl = i∈αₚ
    previousActivation-active {_} {_} {i} p≤t i∈αₚ | no  i∉αₜ | no p≢t   with ≤+≢⇒< p≤t p≢t
    ... | s≤s p≤t₂ = previousActivation-active p≤t₂ i∈αₚ

    previousActivation-mostRecent : ∀ {t p i} (p≤t : p ≤ t) (i∈αₚ : i ∈ α p) → ∀ {t'} → t' ≤ t → i ∈ α t' → t' ≤ previousActivation p≤t i∈αₚ
    previousActivation-mostRecent {t} {p} {i} _ _ with i ∈? α t | p ≟ t
    previousActivation-mostRecent {t}         p≤t _    | yes i∈αₜ | _        = λ t''≤t _ → t''≤t
    previousActivation-mostRecent {t}         p≤t i∈αₚ | no  _    | yes refl = λ t''≤t _ → t''≤t
    previousActivation-mostRecent {_} {_} {i} p≤t i∈αₚ | no  i∉αₜ | no p≢t   with ≤+≢⇒< p≤t p≢t
    ... | s≤s p≤t₂ = λ t''≤t i∈αₜ'' → (previousActivation-mostRecent p≤t₂ i∈αₚ) (m+1≤n+1⇨m≤n (≤+≢⇒< t''≤t (λ t''≡t → i∉αₜ (subst (λ t → i ∈ α t) t''≡t i∈αₜ'')))) i∈αₜ''

    previousActivation-all : ∀ {t p i} → p ≤ t → i ∈ α p → ∃ λ t' → p ≤ t' × t' ≤ t × i ∈ α t' × (∀ {t''} → t'' ≤ t → i ∈ α t'' → t'' ≤ t')
    previousActivation-all p≤t i∈αₚ = 
      previousActivation p≤t i∈αₚ , 
      previousActivation-after p≤t i∈αₚ , 
      previousActivation-before p≤t i∈αₚ , 
      previousActivation-active p≤t i∈αₚ , 
      previousActivation-mostRecent p≤t i∈αₚ


    ---------------
    -- Data flow --
    ---------------

    -- pointExpiryᵢⱼ≤t

    pointExpiryᵢⱼ≤t-expired : ∀ tᵍ {t} i j {s} → pointExpiryᵢⱼ≤t tᵍ t i j ≤ s → s < t → β s i j ≢ tᵍ
    pointExpiryᵢⱼ≤t-expired tᵍ {zero}  i j {s} _ ()
    pointExpiryᵢⱼ≤t-expired tᵍ {suc t} i j {s} _ _ with β t i j ≟ tᵍ | s ≟ t
    pointExpiryᵢⱼ≤t-expired tᵍ {suc t} i j {_} (s≤s t≤s) (s≤s s<t') | yes _       | _        = contradiction (≤-trans s<t' t≤s) (<-irrefl refl)
    pointExpiryᵢⱼ≤t-expired tᵍ {suc t} i j {_} exp≤s     (s≤s s≤t') | no  βt'ij≢t | yes refl = βt'ij≢t
    pointExpiryᵢⱼ≤t-expired tᵍ {suc t} i j {_} exp≤s     (s≤s s≤t') | no  _       | no  s≢t' = pointExpiryᵢⱼ≤t-expired tᵍ i j exp≤s (≤+≢⇒< s≤t' s≢t')

    -- pointExpiryᵢⱼ

    pointExpiryᵢⱼ-expired : ∀ tᵍ i j {s} → pointExpiryᵢⱼ tᵍ i j ≤ s → β s i j ≢ tᵍ
    pointExpiryᵢⱼ-expired tᵍ i j {s} exp≤s with eventualExpiry tᵍ i j
    ... | (tᶠ , tᶠ-exp) with suc tᶠ ≤? s
    ...   | yes tᶠ<s = tᶠ-exp tᶠ<s
    ...   | no  tᶠ≮s = pointExpiryᵢⱼ≤t-expired tᵍ i j exp≤s (s≤s (≮⇒≥ tᶠ≮s))

    --- expiryᵢⱼ 

    x≤t⇒eₓ≤teₜ : ∀ i j {x t} → x ≤ t → pointExpiryᵢⱼ x i j ≤ expiryᵢⱼ t i j
    x≤t⇒eₓ≤teₜ i j {zero}  {zero}  x≤t rewrite 0-idᵣ-⊔ (pointExpiryᵢⱼ 0 i j) = ≤-refl
    x≤t⇒eₓ≤teₜ i j {suc x} {zero}  ()
    x≤t⇒eₓ≤teₜ i j {x}     {suc t} x≤t with x ≟ suc t
    ... | yes x≡t+1 rewrite x≡t+1 = m≤m⊔n (pointExpiryᵢⱼ (suc t) i j) (expiryᵢⱼ t i j)
    ... | no  x≢t+1 = ≤-trans (x≤t⇒eₓ≤teₜ i j (m+1≤n+1⇨m≤n (≤+≢⇒< x≤t x≢t+1))) (n≤m⊔n (pointExpiryᵢⱼ (suc t) i j) (expiryᵢⱼ t i j))

    expiryᵢⱼ-expired-lemma : ∀ {t t'} i j {x} → expiryᵢⱼ t i j ≤ t' → x ≤ t → β t' i j ≢ x
    expiryᵢⱼ-expired-lemma {zero}  {t'} i j {zero}  ndfₜ≤t' z≤n rewrite 0-idᵣ-⊔ (pointExpiryᵢⱼ zero i j) = pointExpiryᵢⱼ-expired zero i j ndfₜ≤t'
    expiryᵢⱼ-expired-lemma {zero}  {t'} i j {suc x} _      ()
    expiryᵢⱼ-expired-lemma {suc t} {t'} i j {x}     ndfₜ≤t' x≤t+1 with ⊔-sel (pointExpiryᵢⱼ (suc t) i j) (expiryᵢⱼ t i j) | x ≟ suc t
    ... | inj₁ eₜ⊔e≤ₜ≡eₜ  | yes x≡t+1 rewrite eₜ⊔e≤ₜ≡eₜ  | x≡t+1 = pointExpiryᵢⱼ-expired (suc t) i j ndfₜ≤t'
    ... | inj₁ eₜ⊔e≤ₜ≡eₜ  | no  x≢t+1 rewrite eₜ⊔e≤ₜ≡eₜ          = pointExpiryᵢⱼ-expired x       i j (≤-trans (≤-trans (x≤t⇒eₓ≤teₜ i j (m+1≤n+1⇨m≤n (≤+≢⇒< x≤t+1 x≢t+1))) (m⊔n≡m⇨n≤m eₜ⊔e≤ₜ≡eₜ)) ndfₜ≤t')
    ... | inj₂ eₜ⊔e≤ₜ≡e≤ₜ | yes x≡t+1 rewrite eₜ⊔e≤ₜ≡e≤ₜ | x≡t+1 = pointExpiryᵢⱼ-expired (suc t) i j (≤-trans (n⊔m≡m⇨n≤m eₜ⊔e≤ₜ≡e≤ₜ) ndfₜ≤t')
    ... | inj₂ eₜ⊔e≤ₜ≡e≤ₜ | no  x≢t+1 rewrite eₜ⊔e≤ₜ≡e≤ₜ         = expiryᵢⱼ-expired-lemma        i j ndfₜ≤t' (m+1≤n+1⇨m≤n (≤+≢⇒< x≤t+1 x≢t+1))

    expiryᵢⱼ-expired : ∀ t {t'} i j → expiryᵢⱼ t i j ≤ t' → t < β t' i j
    expiryᵢⱼ-expired t {t'} i j ndfₜ≤t' = ∀x≤m:n≢x⇒m<n t (β t' i j) (expiryᵢⱼ-expired-lemma i j ndfₜ≤t')


    -- expiryᵢ

    expiryᵢ-expired : ∀ t {t'} i j → expiryᵢ t i ≤ t' → t < β t' i j
    expiryᵢ-expired t i j fdfₜ≤t' = expiryᵢⱼ-expired t i j (≤-trans (foldr-⊎preserves (expiryᵢⱼ t i j ≤_) ⊔-⊎preserves-x≤ t (tabulate (expiryᵢⱼ t i))
      (inj₂ (anyMap ≤-reflexive (∈-tabulate (expiryᵢⱼ t i) j)))) fdfₜ≤t')

  
    -- expiry

    expiry-expired : ∀ t {t'} i j → expiry t ≤ t' → t < β t' i j
    expiry-expired t i j fdₜ≤t' = expiryᵢ-expired t i j (≤-trans (foldr-⊎preserves (expiryᵢ t i ≤_) ⊔-⊎preserves-x≤ t (tabulate (expiryᵢ t))
      (inj₂ (anyMap ≤-reflexive (∈-tabulate (expiryᵢ t) i)))) fdₜ≤t')

    t≤expiryₜ : ∀ t → t ≤ expiry t
    t≤expiryₜ t = foldr-⊎preserves (t ≤_) ⊔-⊎preserves-x≤ t (tabulate (expiryᵢ t)) (inj₁ ≤-refl)



    -----------
    -- Other --
    -----------

    n≤syncIterₙ : ∀ n → n ≤ syncIter n
    n≤syncIterₙ zero    = z≤n
    n≤syncIterₙ (suc n) = ≤-trans (≤-trans (s≤s (n≤syncIterₙ n)) (s≤s (t≤expiryₜ (syncIter n)))) (nextTotalActivation-after _)

    syncIter-expired : ∀ n i j {t} → syncIter (suc n) ≤ t → syncIter n < β t i j
    syncIter-expired n i j {t} siₙ≤t = expiry-expired (syncIter n) i j (≤-trans (≤-trans (n≤1+n _) (nextTotalActivation-after _)) siₙ≤t)

    syncIter-activated : ∀ n i → ∃ λ t' → syncIter n < t' × t' ≤ syncIter (suc n) × i ∈ α t' × (∀ i j {t''} → t' ≤ t'' → syncIter n < β t'' i j)
    syncIter-activated n i with nextTotalActivation-activated (expiry (syncIter n)) i
    ... | (t' , e[siₙ]<t' , t'≤siₙ₊₁ , i∈αₜ') =
      t' ,
      ≤-trans (s≤s (t≤expiryₜ (syncIter n))) e[siₙ]<t' ,
      t'≤siₙ₊₁ ,
      i∈αₜ' ,
      (λ i j t'≤t'' → expiry-expired (syncIter n) i j (≤-trans (<⇒≤ e[siₙ]<t') t'≤t''))
