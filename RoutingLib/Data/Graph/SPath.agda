open import Level using () renaming (zero to lzero)
open import Data.Fin using (Fin; _<_; _≤_) renaming (zero to fzero; suc to fsuc)
open import Data.Fin.Properties using (_≟_)
open import Data.Nat using (ℕ; zero; suc) renaming (_<_ to _<ℕ_)
open import Data.List using (List; []; _∷_; map)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Binary using (Decidable; Rel)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)

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





  ---------------
  -- All paths --
  ---------------

  infix 4 _∉_ _≈ₚ_ _≉ₚ_

  data SPath (n : ℕ) : Set lzero where
    [] : SPath n
    [_] : NonEmptySPath n → SPath n

  data _∉_ {n : ℕ} : Fin n → SPath n → Set lzero where
    notHere : ∀ {i} → i ∉ []
    notThere : ∀ {i p} → i ∉ₙₑₚ p → i ∉ [ p ]

  _∈_ : ∀ {n} → Fin n → SPath n → Set lzero
  i ∈ p = ¬ (i ∉ p)

  _∉?_ : ∀ {n} → Decidable (_∉_ {n})
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


{-
  toList : ∀ {n} → SPath n → List (Fin n)
  toList [ i ]       = i ∷ []
  toList (i ∷ p ∣ _) = i ∷ toList p

  toVec : ∀ {n} → (p : EPath n) → Vec (Fin n) (suc (length p))
  toVec [ i ]        = i ∷ []
  toVec (i ∷ p ∣ _ ) = i ∷ toVec p
-}
{-  
  lookup : ∀ {n} → (p : EPath n) → Fin (suc (length p)) → (Fin n)
  lookup p fzero = source p
  lookup [ _ ] (fsuc ())
  lookup (i ∷ p ∣ _ ) (fsuc j) = lookup p j
-}

  extendAll : ∀ {n} → List (NonEmptySPath n) → Fin n → List (NonEmptySPath n)
  extendAll []       _ = []
  extendAll (p ∷ ps) i with i ∉ₙₑₚ? p
  ... | no  _   = extendAll ps i
  ... | yes i∉p = i ∷ p ∣ i∉p ∷ extendAll ps i

{-
  allPathsOfLength : ∀ {n} → ℕ → List (NonEmptySPath n)
  allPathsOfLength {n} zero = ? --map [_] (toListᵥ (allFin n))
  allPathsOfLength {n} (suc l) = ? --concat (map (extendAll (allPathsOfLength l)) (toListᵥ (allFin n)))

  allPaths : ∀ {n} → List (NonEmptySPath n)
  allPaths {n} = concat (map allPathsOfLength (map toℕ (toListᵥ (allFin n)))) 
-}
