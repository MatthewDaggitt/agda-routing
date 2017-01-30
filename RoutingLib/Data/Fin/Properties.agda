
open import Data.Fin renaming (zero to fzero; suc to fsuc)
open import Data.Fin.Properties using (toℕ-injective; _≟_)
open import Data.Product using (_,_)
open import Data.Nat using (z≤n; s≤s; zero; suc) renaming (_≤_ to _≤ℕ_; _≤?_ to _≤ℕ?_; ≤-pred to ≤ℕ-pred)
open import Data.Nat.Properties using () renaming (strictTotalOrder to ≤ℕ-strictTotalOrder)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary using (_⇒_; tri<; tri>; tri≈; _Respects₂_; _Respects_; Decidable; Trichotomous; Reflexive; Transitive; Total; Antisymmetric; IsDecTotalOrder; IsTotalOrder; IsPartialOrder; IsStrictTotalOrder; IsPreorder)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; isEquivalence; sym; trans)
open import Relation.Binary.Consequences using (trans∧tri⟶resp≈)
open import Function using (_on_; _∘_; flip)

open import RoutingLib.Data.Nat.Properties using () renaming (m<n⇨m≢n to m<ℕn⇨m≢n; m≰n⇨n<m to m≰ℕn⇨n<m)
open import RoutingLib.Data.Fin

open Relation.Binary.DecTotalOrder Data.Nat.decTotalOrder using () renaming (total to ≤ℕ-total; antisym to ≤ℕ-antisym; refl to ≤ℕ-refl; trans to ≤ℕ-trans)
open Relation.Binary.StrictTotalOrder ≤ℕ-strictTotalOrder using () renaming (compare to ≤ℕ-tri)

module RoutingLib.Data.Fin.Properties where

  suc≢zero : ∀ {n} {i : Fin n} → fsuc i ≢ fzero
  suc≢zero ()

  suc-injective : ∀ {n} {x y : Fin n} → fsuc x ≡ fsuc y → x ≡ y
  suc-injective refl = refl

  inject₁-injective₁ : ∀ {n} {i j : Fin n} → inject₁ i ≡ inject₁ j → i ≡ j
  inject₁-injective₁ {i = fzero}  {fzero}  i≡j = refl
  inject₁-injective₁ {i = fzero}  {fsuc j} ()
  inject₁-injective₁ {i = fsuc i} {fzero}  ()
  inject₁-injective₁ {i = fsuc i} {fsuc j} i≡j = cong fsuc (inject₁-injective₁ (suc-injective i≡j))

  inject₁-injective₂ : ∀ {n} {i j : Fin n} → i ≢ j → inject₁ i ≢ inject₁ j
  inject₁-injective₂ i≢j i≡j = i≢j (inject₁-injective₁ i≡j)


  toℕ-injective₂ : ∀ {n} {i j : Fin n} → i ≢ j → toℕ i ≢ toℕ j
  toℕ-injective₂ i≢j toℕi≡toℕj = i≢j (toℕ-injective toℕi≡toℕj)

  _≤?_ : ∀ {n} → Decidable (_≤_ {n = n})
  x ≤? y = toℕ x ≤ℕ? toℕ y 

  _<?_ : ∀ {n} → Decidable (_<_ {n = n})
  x <? y = suc (toℕ x) ≤ℕ? toℕ y



  -------------------------
  -- Ordering properties --
  -------------------------

  ≤-reflexive : ∀ {n} → _≡_ ⇒ (_≤_ {n})
  ≤-reflexive refl = ≤ℕ-refl

  ≤-refl : ∀ {n} → Reflexive (_≤_ {n})
  ≤-refl {x = fzero} = z≤n
  ≤-refl {x = fsuc n} = s≤s ≤-refl

  ≤-trans : ∀ {n} → Transitive (_≤_ {n})
  ≤-trans = ≤ℕ-trans

  ≤-antisym : ∀ {n} → Antisymmetric _≡_ (_≤_ {n})
  ≤-antisym x≤y y≤x = toℕ-injective (≤ℕ-antisym x≤y y≤x)
  
  ≤-total : ∀ {n} → Total (_≤_ {n})
  ≤-total x y = ≤ℕ-total (toℕ x) (toℕ y)

  ≤-respₗ-≡ : ∀ {n x} → ((_≤_ {n}) x) Respects _≡_
  ≤-respₗ-≡ refl x≤y = x≤y

  ≤-respᵣ-≡ : ∀ {n x} → (flip (_≤_ {n}) x) Respects _≡_
  ≤-respᵣ-≡ refl x≤y = x≤y

  ≤-resp₂-≡ : ∀ {n} → (_≤_ {n}) Respects₂ _≡_
  ≤-resp₂-≡ = ≤-respₗ-≡ , ≤-respᵣ-≡

  ≤-isPreorder : ∀{n} → IsPreorder _≡_ (_≤_ {n})
  ≤-isPreorder = record { 
      isEquivalence = isEquivalence;
      reflexive = ≤-reflexive;
      trans = ≤-trans 
    }

  ≤-isPartialOrder : ∀{n} → IsPartialOrder _≡_ (_≤_ {n})
  ≤-isPartialOrder = record { 
      isPreorder = ≤-isPreorder;
      antisym = ≤-antisym
    }

  ≤-isTotalOrder : ∀ {n} → IsTotalOrder _≡_ (_≤_ {n})
  ≤-isTotalOrder = record { 
      isPartialOrder = ≤-isPartialOrder ; 
      total = ≤-total 
    }

  ≤-isDecTotalOrder : ∀ {n} → IsDecTotalOrder _≡_ (_≤_ {n})
  ≤-isDecTotalOrder = record { 
      isTotalOrder = ≤-isTotalOrder ;
      _≟_ = _≟_ ;
      _≤?_ = _≤?_ 
    }

  cmp : ∀ {n} → Trichotomous _≡_ (_<_ {n})
  cmp fzero    fzero    = tri≈ (λ())     refl  (λ())
  cmp fzero    (fsuc j) = tri< (s≤s z≤n) (λ()) (λ())
  cmp (fsuc i) fzero    = tri> (λ())     (λ()) (s≤s z≤n)
  cmp (fsuc i) (fsuc j) with cmp i j
  ... | tri<  lt ¬eq ¬gt = tri< (s≤s lt)         (¬eq ∘ suc-injective) (¬gt ∘ ≤ℕ-pred)
  ... | tri> ¬lt ¬eq  gt = tri> (¬lt ∘ ≤ℕ-pred) (¬eq ∘ suc-injective) (s≤s gt)
  ... | tri≈ ¬lt  eq ¬gt = tri≈ (¬lt ∘ ≤ℕ-pred) (cong fsuc eq)    (¬gt ∘ ≤ℕ-pred)


  -----------
  -- Other --
  -----------

  m<n⇨m≢n : ∀ {n₁} {m n : Fin n₁} → m < n → m ≢ n
  m<n⇨m≢n m<n m≡n = (m<ℕn⇨m≢n m<n) (cong toℕ m≡n)

  m≰n⇨m≢n : ∀ {n₁} {m n : Fin n₁} → ¬ (m ≤ n) → m ≢ n
  m≰n⇨m≢n m≰n refl = m≰n ≤ℕ-refl
  
  m≰n⇨n<m : ∀ {n₁} {m n : Fin n₁} → ¬ (m ≤ n) → n < m
  m≰n⇨n<m m≰n = m≰ℕn⇨n<m m≰n




  -- Punchout

  punchdown-injective : ∀ {m} {i j k : Fin (suc m)} (i≢j : i ≢ j) (i≢k : i ≢ k) → punchdown i≢j ≡ punchdown i≢k → j ≡ k
  punchdown-injective {_}     {fzero}   {fzero}  {_}      i≢j _   _    = contradiction refl i≢j
  punchdown-injective {_}     {fzero}   {_}      {fzero}  _   i≢k _    = contradiction refl i≢k
  punchdown-injective {_}     {fzero}   {fsuc j} {fsuc k} _   _   pⱼ≡pₖ = cong fsuc pⱼ≡pₖ
  punchdown-injective {zero}  {fsuc ()}
  punchdown-injective {suc n} {fsuc i}  {fzero}  {fzero}  _   _    _   = refl
  punchdown-injective {suc n} {fsuc i}  {fzero}  {fsuc k} _   _   ()
  punchdown-injective {suc n} {fsuc i}  {fsuc j} {fzero}  _   _   ()
  punchdown-injective {suc n} {fsuc i}  {fsuc j} {fsuc k} i≢j i≢k pⱼ≡pₖ = cong fsuc (punchdown-injective (i≢j ∘ cong fsuc) (i≢k ∘ cong fsuc) (suc-injective pⱼ≡pₖ))

  punchdown-cong : ∀ {m} {i j k : Fin (suc m)} (i≢j : i ≢ j) (i≢k : i ≢ k) → j ≡ k → punchdown i≢j ≡ punchdown i≢k
  punchdown-cong {_} i≢j i≢k refl = refl

  punchup-injective : ∀ {m} k {i j : Fin m} → punchup k i ≡ punchup k j → i ≡ j
  punchup-injective fzero                      i+1≡j+1   = suc-injective i+1≡j+1
  punchup-injective (fsuc k) {fzero}  {fzero}  _         = refl
  punchup-injective (fsuc k) {fzero}  {fsuc j} ()
  punchup-injective (fsuc k) {fsuc i} {fzero}  ()
  punchup-injective (fsuc k) {fsuc i} {fsuc j} ↑i+1≡↑j+1 = cong fsuc (punchup-injective k (suc-injective ↑i+1≡↑j+1))

  punchupₖ≢k : ∀ {m} k {i : Fin m} → punchup k i ≢ k
  punchupₖ≢k fzero            ()
  punchupₖ≢k (fsuc k) {fzero} ()
  punchupₖ≢k (fsuc k) {fsuc i} = punchupₖ≢k k ∘ suc-injective

  punchdown-punchup : ∀ {m} {i j : Fin (suc m)} (i≢j : i ≢ j) → punchup i (punchdown i≢j) ≡ j
  punchdown-punchup {_} {fzero} {fzero} 0≢0 = contradiction refl 0≢0
  punchdown-punchup {_} {fzero} {fsuc j} _ = refl
  punchdown-punchup {zero} {fsuc ()}
  punchdown-punchup {suc m} {fsuc i} {fzero} i≢j  = refl
  punchdown-punchup {suc m} {fsuc i} {fsuc j} i≢j = cong fsuc (punchdown-punchup (i≢j ∘ cong fsuc))

