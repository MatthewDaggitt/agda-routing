open import Level using () renaming (zero to lzero)
open import Data.Fin using (Fin; _<_; _≤_) renaming (zero to fzero; suc to fsuc)
open import Data.Fin.Properties using (_≟_)
open import Data.Nat using (ℕ; zero; suc; _≤?_; z≤n; s≤s) renaming (_<_ to _<ℕ_)
open import Data.Nat.Properties using (≰⇒>)
open import Data.Product using (_,_)
open import Data.List using (List; []; _∷_; map)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary using (Decidable; Rel)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; cong)
open import Function using (_∘_)

open import RoutingLib.Data.Graph
open import RoutingLib.Data.Fin.Pigeonhole using (pigeonhole)

module RoutingLib.Data.Graph.SPath where

  ---------------------
  -- Non-empty paths --
  ---------------------

  infix 4 _∉ₙₑₚ_ _≈ₙₑₚ_ _≤ₙₑₚ_

  data NonEmptySPath (n : ℕ) : Set lzero
  data _∉ₙₑₚ_ {n : ℕ} : Fin n → NonEmptySPath n → Set lzero

  data NonEmptySPath (n : ℕ) where
    _∺_∣_ : ∀ (i j : Fin n) → i ≢ j → NonEmptySPath n
    _∷_∣_ : ∀ i p → i ∉ₙₑₚ p → NonEmptySPath n

  data _∉ₙₑₚ_ {n : ℕ} where
    notThere : ∀ {i j k i≢j} → k ≢ i → k ≢ j   → k ∉ₙₑₚ i ∺ j ∣ i≢j
    notHere  : ∀ {i p k i∉p} → k ≢ i → k ∉ₙₑₚ p → k ∉ₙₑₚ i ∷ p ∣ i∉p

  _∉ₙₑₚ?_ : ∀ {n} → Decidable (_∉ₙₑₚ_ {n})
  k ∉ₙₑₚ? (i ∺ j ∣ _) with k ≟ i | k ≟ j
  ... | yes k≡i | _       = no λ{(notThere k≢i _) → k≢i k≡i}
  ... | _       | yes k≡j = no λ{(notThere _ k≢j) → k≢j k≡j}
  ... | no  k≢i | no  k≢j = yes (notThere k≢i k≢j)
  k ∉ₙₑₚ? (i ∷ p ∣ _) with k ≟ i | k ∉ₙₑₚ? p
  ... | yes i≡j | _       = no λ{(notHere i≢j _) → i≢j i≡j }
  ... | _       | no  i∈p = no λ{(notHere _ i∉p) → i∈p i∉p}
  ... | no  i≢j | yes i∉p = yes (notHere i≢j i∉p)


  data _≈ₙₑₚ_ {n : ℕ} : Rel (NonEmptySPath n) lzero where
    _∺_ : ∀ {i j k l i≢j k≢l} → i ≡ k → j ≡ l → (i ∺ j ∣ i≢j) ≈ₙₑₚ (k ∺ l ∣ k≢l)
    _∷_ : ∀ {i j p q i∉p j∉q} → i ≡ j → p ≈ₙₑₚ q → (i ∷ p ∣ i∉p) ≈ₙₑₚ (j ∷ q ∣ j∉q)

  data _≤ₙₑₚ_ {n : ℕ} : Rel (NonEmptySPath n) lzero where
    stopFirst   : ∀ {i j k l i≢j k≢l} → i ≡ k → j ≤ l → i ∺ j ∣ i≢j ≤ₙₑₚ k ∺ l ∣ k≢l
    stopSecond  : ∀ {i j k l i≢j k≢l} → i < k → i ∺ j ∣ i≢j ≤ₙₑₚ k ∺ l ∣ k≢l
    stepUnequal : ∀ {i j p q i∉p j∉q} → i < j → i ∷ p ∣ i∉p ≤ₙₑₚ j ∷ q ∣ j∉q
    stepEqual   : ∀ {i j p q i∉p j∉q} → i ≡ j → p ≤ₙₑₚ q → i ∷ p ∣ i∉p ≤ₙₑₚ j ∷ q ∣ j∉q



  -- Operations

  source : ∀ {n} → NonEmptySPath n → Fin n
  source (i ∺ _ ∣ _) = i
  source (i ∷ _ ∣ _) = i

  destination : ∀ {n} → NonEmptySPath n → Fin n
  destination (_ ∺ j ∣ _) = j
  destination (_ ∷ p ∣ _) = destination p

  length : ∀ {n} → NonEmptySPath n → ℕ
  length (_ ∺ _ ∣ _) = 1
  length (_ ∷ p ∣ _) = suc (length p)

  private

    lookup : ∀ {n} → (p : NonEmptySPath n) → Fin (suc (length p)) → Fin n
    lookup (i ∺ j ∣ _) fzero            = i
    lookup (i ∺ j ∣ _) (fsuc fzero)     = j
    lookup (i ∺ j ∣ _) (fsuc (fsuc ()))
    lookup (i ∷ p ∣ _) fzero            = i
    lookup (i ∷ p ∣ _) (fsuc k)         = lookup p k

    lookup-∈ : ∀ {n} → (p : NonEmptySPath n) → ∀ i {k} → lookup p i ≡ k → ¬ (k ∉ₙₑₚ p)
    lookup-∈ (i ∺ j ∣ _) fzero            refl (notThere i≢i _) = i≢i refl
    lookup-∈ (i ∺ j ∣ _) (fsuc fzero)     refl (notThere _ j≢j) = j≢j refl
    lookup-∈ (i ∺ j ∣ _) (fsuc (fsuc ()))
    lookup-∈ (i ∷ p ∣ _) fzero            refl (notHere i≢i _)  = i≢i refl
    lookup-∈ (i ∷ p ∣ _) (fsuc k)         pᵢ≡k  (notHere _ i∉p)  = lookup-∈ p k pᵢ≡k i∉p

    lookup! : ∀ {n} (p : NonEmptySPath n) {k l} → k ≢ l → lookup p k ≢ lookup p l
    lookup! _             {fzero}          {fzero}          0≢0 _ = 0≢0 refl
    lookup! (i ∺ j ∣ i≢j) {fzero}          {fsuc fzero}     _     = i≢j
    lookup! (i ∺ j ∣ i≢j) {fsuc fzero}     {fzero}          _     = i≢j ∘ sym
    lookup! (i ∺ j ∣ x)   {_}              {fsuc (fsuc ())} _
    lookup! (i ∺ j ∣ x)   {fsuc (fsuc ())} {_}
    lookup! (i ∺ j ∣ x)   {fsuc fzero}     {fsuc fzero}     1≢1 _ = 1≢1 refl
    lookup! (i ∷ p ∣ i∉p) {fzero}          {fsuc j}         i≢j i≡pⱼ = contradiction i∉p (lookup-∈ p j (sym i≡pⱼ))
    lookup! (i ∷ p ∣ i∉p) {fsuc k}         {fzero}          i≢j pₖ≡i = contradiction i∉p (lookup-∈ p k pₖ≡i)
    lookup! (i ∷ p ∣ x)   {fsuc k}         {fsuc l}         k+1≢l+1 pₖ≡pₗ = lookup! p (k+1≢l+1 ∘ cong fsuc) pₖ≡pₗ

  |p|ₙₑₚ<n : ∀ {n} (p : NonEmptySPath n) → length p <ℕ n
  |p|ₙₑₚ<n {n} p with suc (length p) ≤? n
  ... | yes |p|<n = |p|<n
  ... | no  |p|≮n with pigeonhole (≰⇒> |p|≮n) (lookup p)
  ...   | i , j , i≢j , pᵢ≡pⱼ = contradiction pᵢ≡pⱼ (lookup! p i≢j)



  ---------------
  -- All paths --
  ---------------

  infix 4 _∉ₚ_ _≈ₚ_ _≉ₚ_

  data SPath (n : ℕ) : Set lzero where
    [] : SPath n
    [_] : NonEmptySPath n → SPath n

  data _∉ₚ_ {n : ℕ} : Fin n → SPath n → Set lzero where
    notHere : ∀ {i} → i ∉ₚ []
    notThere : ∀ {i p} → i ∉ₙₑₚ p → i ∉ₚ [ p ]

  _∈_ : ∀ {n} → Fin n → SPath n → Set lzero
  i ∈ p = ¬ (i ∉ₚ p)

  _∉?_ : ∀ {n} → Decidable (_∉ₚ_ {n})
  k ∉? []    = yes notHere
  k ∉? [ p ] with k ∉ₙₑₚ? p
  ... | yes k∉p = yes (notThere k∉p)
  ... | no  k∈p = no λ{(notThere k∉p) → k∈p k∉p}

  -- Equality

  data _≈ₚ_ {n : ℕ} : Rel (SPath n) lzero where
    [] : [] ≈ₚ []
    [_] : ∀ {p q} → p ≈ₙₑₚ q → [ p ] ≈ₚ [ q ]

  _≉ₚ_ : ∀ {n} → Rel (SPath n) lzero
  xs ≉ₚ ys = ¬ (xs ≈ₚ ys)

  -- Orderings

  infix 4 _≤ₚ_ _≰ₚ_

  data _≤ₚ_ {n : ℕ} : Rel (SPath n) lzero where
    stop : ∀ {p} → [] ≤ₚ p
    len  : ∀ {p} {q} → length p <ℕ length q → [ p ] ≤ₚ [ q ]
    lex  : ∀ {p} {q} → length p ≡ length q → p ≤ₙₑₚ q → [ p ] ≤ₚ [ q ]

  _≰ₚ_ : ∀ {n} → Rel (SPath n) lzero
  p ≰ₚ q = ¬ (p ≤ₚ q)



  ----------------
  -- Operations --
  ----------------


  lengthₚ : ∀ {n} → SPath n → ℕ
  lengthₚ [] = 0
  lengthₚ [ p ] = length p

  lengthₚ<n : ∀ {n} (p : SPath (suc n)) → lengthₚ p <ℕ (suc n)
  lengthₚ<n []    = s≤s z≤n
  lengthₚ<n [ p ] = |p|ₙₑₚ<n p
