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

open import RoutingLib.Asynchronous.Core
open import RoutingLib.Data.Nat.Properties using (cmp; ≤+≢⇒<; m<n≤o⇨o∸n<o∸m; ≤-refl; <⇒≤; ⊔-⊎preserves-x≤; ∀x≤m:n≢x⇒m<n; 0-idᵣ-⊔; <-irrefl; ≤-trans; ≤-reflexive; ≮⇒≥; m⊔n≡m⇨n≤m; n⊔m≡m⇨n≤m; n≤m⊔n; m+1≤n+1⇨m≤n)
open import RoutingLib.Induction.Nat using () renaming (<-well-founded to <-wf)
open import RoutingLib.Data.List.Folds using (foldr-⊎preserves)
open import RoutingLib.Data.List using (allFin; descending)
open import RoutingLib.Data.List.Any.Properties using (map⁺)
open import RoutingLib.Data.List.Any.PropositionalMembership using (∈-allFin; ∈-map)

module RoutingLib.Asynchronous.Properties {p : ℕ} (sch : AdmissableSchedule p) where

  open AdmissableSchedule sch


  -- The next activation time
  private

    nextActivation' : ∀ {t t' i} → Acc _<_ (t' ∸ t) → t < t' → i ∈ α t' → ∃ λ tₐ → (t < tₐ) × (i ∈ α tₐ) × (∀ {t''} → t < t'' → i ∈ α t'' → tₐ ≤ t'')
    nextActivation' {t} {t'} {i} (acc t'∸t-acc) t<t' i∈αₜ' with i ∈? α (suc t) | (suc t) ≟ t'
    ... | yes i∈αₜ₊₁ | _          = suc t , ≤-refl , i∈αₜ₊₁ , (λ t<t'' _ → t<t'')
    ... | no  i∉αₜ₊₁ | yes t+1≡t' = contradiction (subst (λ t → i ∈ α t) (sym t+1≡t') i∈αₜ') i∉αₜ₊₁
    ... | no  i∉αₜ₊₁ | no  t+1≢t' with nextActivation' (t'∸t-acc (t' ∸ suc t) (m<n≤o⇨o∸n<o∸m ≤-refl t<t')) (≤+≢⇒< t<t' t+1≢t') i∈αₜ'
    ...   | tₐ , t+1<tₐ , i∈αₜₐ , earliest = tₐ , <⇒≤ t+1<tₐ , i∈αₜₐ , (λ {t''} t<t'' i∈αₜ'' → earliest (≤+≢⇒< t<t'' (λ t+1≡t'' → i∉αₜ₊₁ (subst (λ t → i ∈ α t) (sym t+1≡t'') i∈αₜ''))) i∈αₜ'')

  nextActivation-all : ∀ t i → ∃ λ tₐ → (t < tₐ) × (i ∈ α tₐ) × (∀ {t''} → t < t'' → i ∈ α t'' → tₐ ≤ t'')
  nextActivation-all t i with infiniteActivation t i
  ... | (t' , t<t' , i∈αₜ') = nextActivation' (<-wf (t' ∸ t)) t<t' i∈αₜ'

  nextActivation : ℕ → Fin p → ℕ
  nextActivation t i = proj₁ (nextActivation-all t i)

  nextActivation-after : ∀ t i → t < nextActivation t i
  nextActivation-after t i = proj₁ (proj₂ (nextActivation-all t i))

  nextActivation-active : ∀ t i → i ∈ α (nextActivation t i)
  nextActivation-active t i = proj₁ (proj₂ (proj₂ (nextActivation-all t i)))

  nextActivation-next : ∀ {t i t''} → t < t'' → i ∈ α t'' → nextActivation t i ≤ t''
  nextActivation-next {t} {i} = proj₂ (proj₂ (proj₂ (nextActivation-all t i)))



  -- Time after t at which all nodes have activated

  allActivations : ℕ → ℕ
  allActivations t = foldr _⊔_ (suc t) (map (nextActivation t) (allFin p))

  allActivations-after : ∀ t → t < allActivations t
  allActivations-after t = foldr-⊎preserves (t <_) ⊔-⊎preserves-x≤ (suc t) (map (nextActivation t) (allFin p)) (inj₁ ≤-refl)

  allActivations-activated : ∀ t i → ∃ λ t' → t < t' × t' ≤ allActivations t × i ∈ α t'
  allActivations-activated t i = nextActivation t i , nextActivation-after t i , foldr-⊎preserves (nextActivation t i ≤_) ⊔-⊎preserves-x≤ (suc t) (map (nextActivation t) (allFin p)) (inj₂ (anyMap ≤-reflexive (∈-map (nextActivation t) (∈-allFin i)))) , nextActivation-active t i

  -- Most recent activation time before time n

  previousActivation-all : ∀ {t p i} → p ≤ t → i ∈ α p → ∃ λ t' → p ≤ t' × t' ≤ t × i ∈ α t' × (∀ {t''} → t'' ≤ t → i ∈ α t'' → t'' ≤ t')
  previousActivation-all {t} {p} {i} _ _ with i ∈? α t | p ≟ t
  previousActivation-all {t}         p≤t _    | yes i∈αₜ | _       =  t , p≤t , ≤-refl , i∈αₜ , (λ t''≤t _ → t''≤t)
  previousActivation-all {t}         p≤t i∈αₚ | _        | yes refl = t , p≤t , ≤-refl , i∈αₚ , (λ t''≤t _ → t''≤t)
  previousActivation-all {_} {_} {i} p≤t i∈αₚ | no i∉αₜ   | no p≢t   with ≤+≢⇒< p≤t p≢t
  ... | s≤s p≤t₂ with previousActivation-all p≤t₂ i∈αₚ
  ...   | (t' , p≤t' , t'≤t , i∈αₜ' , latest) = t' , latest p≤t₂ i∈αₚ , ≤-trans t'≤t (n≤1+n _) , i∈αₜ' , (λ t''≤t i∈αₜ'' → latest (m+1≤n+1⇨m≤n (≤+≢⇒< t''≤t (λ t''≡t → i∉αₜ (subst (λ t → i ∈ α t) t''≡t i∈αₜ'')))) i∈αₜ'')

  previousActivation : ∀ {t p i} → p ≤ t → i ∈ α p → ℕ
  previousActivation p≤t i∈αₚ = proj₁ (previousActivation-all p≤t i∈αₚ)

  previousActivation-before : ∀ {t p i} (p≤t : p ≤ t) (i∈αₚ : i ∈ α p) → previousActivation p≤t i∈αₚ ≤ t
  previousActivation-before p≤t i∈αₚ = proj₁ (proj₂ (proj₂ (previousActivation-all p≤t i∈αₚ)))

  previousActivation-active : ∀ {t p i} (p≤t : p ≤ t) (i∈αₚ : i ∈ α p) → i ∈ α (previousActivation p≤t i∈αₚ)
  previousActivation-active p≤t i∈αₚ = proj₁ (proj₂ (proj₂ (proj₂ (previousActivation-all p≤t i∈αₚ))))

  previousActivation-mostRecent : ∀ {t p i} (p≤t : p ≤ t) (i∈αₚ : i ∈ α p) → ∀ {t'} → t' ≤ t → i ∈ α t' → t' ≤ previousActivation p≤t i∈αₚ
  previousActivation-mostRecent p≤t i∈αₚ = proj₂ (proj₂ (proj₂ (proj₂ (previousActivation-all p≤t i∈αₚ))))



  -- The first time before time t' that information generated at j at time t is not used again by i before time t'

  boundedExpiration : ℕ → ℕ → Fin p → Fin p → ℕ
  boundedExpiration zero t i j = zero
  boundedExpiration (suc t') t i j with β t' i j ≟ t
  ... | yes _ = suc t'
  ... | no  _ = boundedExpiration t' t i j

  boundedExpiration-expiry : ∀ {t'} t i j → ∀ {s} → boundedExpiration t' t i j ≤ s → s < t' → β s i j ≢ t
  boundedExpiration-expiry {zero}   _ _ _ _ ()
  boundedExpiration-expiry {suc t'} t i j {s} _ _ with β t' i j ≟ t | s ≟ t'
  boundedExpiration-expiry {suc t'} t i j (s≤s t'≤s) (s≤s s<t') | yes _       | _        = contradiction (≤-trans s<t' t'≤s) (<-irrefl refl)
  boundedExpiration-expiry {suc t'} t i j exp≤s      (s≤s s≤t') | no  βt'ij≢t | yes refl = βt'ij≢t
  boundedExpiration-expiry {suc t'} t i j exp≤s      (s≤s s≤t') | no  _       | no  s≢t' = boundedExpiration-expiry {t'} t i j exp≤s (≤+≢⇒< s≤t' s≢t')



  -- The first time that information generated at j at time t is not used again by i

  dataNotFrom : ℕ → Fin p → Fin p → ℕ
  dataNotFrom t i j with eventualExpiry t i j
  ... | (tᶠ , tᶠ-exp) = boundedExpiration (suc tᶠ) t i j

  dataNotFrom-expiry : ∀ t i j {s} → dataNotFrom t i j ≤ s → β s i j ≢ t
  dataNotFrom-expiry t i j {s} exp≤s with eventualExpiry t i j
  ... | (tᶠ , tᶠ-exp) with suc tᶠ ≤? s
  ...   | yes tᶠ<s = tᶠ-exp tᶠ<s
  ...   | no  tᶠ≮s = boundedExpiration-expiry {t' = suc tᶠ} t i j exp≤s (s≤s (≮⇒≥ tᶠ≮s))



  --- The first time that information generated at j before or at time t is not used again by i
  newerDataFrom : ℕ → Fin p → Fin p → ℕ
  newerDataFrom t i j = foldr _⊔_ 0 (map (λ t → dataNotFrom t i j) (descending (suc t)))

  x≤t⇒eₓ≤teₜ : ∀ i j {x t} → x ≤ t → dataNotFrom x i j ≤ newerDataFrom t i j
  x≤t⇒eₓ≤teₜ i j {zero}  {zero}  x≤t rewrite 0-idᵣ-⊔ (dataNotFrom 0 i j) = ≤-refl
  x≤t⇒eₓ≤teₜ i j {suc x} {zero}  ()
  x≤t⇒eₓ≤teₜ i j {x}     {suc t} x≤t with x ≟ suc t
  ... | yes x≡t+1 rewrite x≡t+1 = m≤m⊔n (dataNotFrom (suc t) i j) (newerDataFrom t i j)
  ... | no  x≢t+1 = ≤-trans (x≤t⇒eₓ≤teₜ i j (m+1≤n+1⇨m≤n (≤+≢⇒< x≤t x≢t+1))) (n≤m⊔n (dataNotFrom (suc t) i j) (newerDataFrom t i j))

  newerDataFrom-lemma : ∀ {t t'} i j {x} → newerDataFrom t i j ≤ t' → x ≤ t → β t' i j ≢ x
  newerDataFrom-lemma {zero}  {t'} i j {zero}  ndfₜ≤t' z≤n rewrite 0-idᵣ-⊔ (dataNotFrom zero i j) = dataNotFrom-expiry zero i j ndfₜ≤t'
  newerDataFrom-lemma {zero}  {t'} i j {suc x} _      ()
  newerDataFrom-lemma {suc t} {t'} i j {x}     ndfₜ≤t' x≤t+1 with ⊔-sel (dataNotFrom (suc t) i j) (newerDataFrom t i j) | x ≟ suc t
  ... | inj₁ eₜ⊔e≤ₜ≡eₜ  | yes x≡t+1 rewrite eₜ⊔e≤ₜ≡eₜ  | x≡t+1 = dataNotFrom-expiry (suc t) i j ndfₜ≤t'
  ... | inj₁ eₜ⊔e≤ₜ≡eₜ  | no  x≢t+1 rewrite eₜ⊔e≤ₜ≡eₜ          = dataNotFrom-expiry x       i j (≤-trans (≤-trans (x≤t⇒eₓ≤teₜ i j (m+1≤n+1⇨m≤n (≤+≢⇒< x≤t+1 x≢t+1))) (m⊔n≡m⇨n≤m eₜ⊔e≤ₜ≡eₜ)) ndfₜ≤t')
  ... | inj₂ eₜ⊔e≤ₜ≡e≤ₜ | yes x≡t+1 rewrite eₜ⊔e≤ₜ≡e≤ₜ | x≡t+1 = dataNotFrom-expiry (suc t) i j (≤-trans (n⊔m≡m⇨n≤m eₜ⊔e≤ₜ≡e≤ₜ) ndfₜ≤t')
  ... | inj₂ eₜ⊔e≤ₜ≡e≤ₜ | no  x≢t+1 rewrite eₜ⊔e≤ₜ≡e≤ₜ         = newerDataFrom-lemma        i j ndfₜ≤t' (m+1≤n+1⇨m≤n (≤+≢⇒< x≤t+1 x≢t+1))

  newerDataFrom-expiry : ∀ t t' i j → newerDataFrom t i j ≤ t' → t < β t' i j
  newerDataFrom-expiry t t' i j ndfₜ≤t' = ∀x≤m:n≢x⇒m<n t (β t' i j) (newerDataFrom-lemma i j ndfₜ≤t')





  -- The time at which node i only uses data generated after time t

  freshDataFor : ℕ → Fin p → ℕ
  freshDataFor t i = foldr _⊔_ t (map (newerDataFrom t i) (allFin p))

  freshDataFor-expiry : ∀ t t' i j → freshDataFor t i ≤ t' → t < β t' i j
  freshDataFor-expiry t t' i j fdfₜ≤t' = newerDataFrom-expiry t t' i j (≤-trans (foldr-⊎preserves (newerDataFrom t i j ≤_) ⊔-⊎preserves-x≤ t (map (newerDataFrom t i) (allFin p))
    (inj₂ (anyMap ≤-reflexive (∈-map (newerDataFrom t i) (∈-allFin j))))) fdfₜ≤t')



  -- The time at which all nodes only use data generated after time t

  freshData : ℕ → ℕ
  freshData t = foldr _⊔_ t (map (freshDataFor t) (allFin p))

  t≤freshData : ∀ t → t ≤ freshData t
  t≤freshData t = foldr-⊎preserves (t ≤_) ⊔-⊎preserves-x≤ t (map (freshDataFor t) (allFin p)) (inj₁ ≤-refl)

  freshData-expiry : ∀ t t' i j → freshData t ≤ t' → t < β t' i j
  freshData-expiry t t' i j fdₜ≤t' = freshDataFor-expiry t t' i j (≤-trans (foldr-⊎preserves (freshDataFor t i ≤_) ⊔-⊎preserves-x≤ t (map (freshDataFor t) (allFin p))
    (inj₂ (anyMap ≤-reflexive (∈-map (freshDataFor t) (∈-allFin i))))) fdₜ≤t')



  -- Time at which i has performed the n complete "synchronous" iterations occurred

  abstract

    syncIter : ℕ → ℕ
    syncIter zero    = zero
    syncIter (suc t) = allActivations (freshData (syncIter t))

    syncIter-activated : ∀ t i → ∃ λ t' → syncIter t < t' × t' ≤ syncIter (suc t) × i ∈ α t' × (∀ i j {t''} → t' ≤ t'' → syncIter t < β t'' i j)
    syncIter-activated t i with allActivations-activated (freshData (syncIter t)) i
    ... | (t' , fd[si]ₜ<t' , t'≤siₜ₊₁ , i∈αₜ') =
      t' ,
      ≤-trans (s≤s (t≤freshData (syncIter t))) fd[si]ₜ<t' ,
      t'≤siₜ₊₁ ,
      i∈αₜ' ,
      (λ i j {t''} t'≤t'' → freshData-expiry (syncIter t) t'' i j (≤-trans (<⇒≤ fd[si]ₜ<t') t'≤t''))

    syncIter-lowerBound : ∀ n → n ≤ syncIter n
    syncIter-lowerBound zero    = z≤n
    syncIter-lowerBound (suc n) =
      begin
        suc n
      ≤⟨ s≤s (syncIter-lowerBound n) ⟩
        suc (syncIter n)
      ≤⟨ s≤s (t≤freshData (syncIter n)) ⟩
        suc (freshData (syncIter n))
      ≤⟨ allActivations-after (freshData (syncIter n)) ⟩
        allActivations (freshData (syncIter n))
      ∎
      where open ≤-Reasoning

    syncIter-data : ∀ n i j t → syncIter (suc n) ≤ t → syncIter n < β t i j
    syncIter-data n i j t siₙ≤t = freshData-expiry (syncIter n) t i j (
      begin
        freshData (syncIter n)
      ≤⟨ n≤1+n (freshData (syncIter n)) ⟩
        suc (freshData (syncIter n))
      ≤⟨ allActivations-after (freshData (syncIter n)) ⟩
        allActivations (freshData (syncIter n))
      ≤⟨ siₙ≤t ⟩
        t
      ∎)
      where open ≤-Reasoning
