open import Level using () renaming (zero to lzero)
open import Data.Fin using (Fin; _≤_; _<_; toℕ) renaming (zero to fzero; suc to fsuc)
open import Data.Fin.Properties using (_≟_)
open import Data.Nat using (ℕ; zero; suc) renaming (_<_ to _<ℕ_)
open import Data.List using (List; []; _∷_; map; concat; gfilter)
open import Data.Product using (_×_; _,_)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Binary using (Decidable; Rel)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)
open import Function using (_∘_)

open import RoutingLib.Data.Graph
open import RoutingLib.Data.List using (allFin; combine)

module RoutingLib.Data.Graph.SGPath {a n} {A : Set a} where

  ---------------------
  -- Non-empty paths --
  ---------------------

  infix 4 _∉ₙₑₚ_ _≈ₙₑₚ_ _≤ₙₑₚ_

  data NonEmptySGPath (G : Graph A n) : Set a
  data _∉ₙₑₚ_ {G} : Fin n → NonEmptySGPath G → Set a
  source : ∀ {G} → NonEmptySGPath G → Fin n

  data NonEmptySGPath (G : Graph A n) where
    _∺_∣_∣_ : ∀ (i j : Fin n) → i ≢ j → (i , j) ᵉ∈ᵍ G → NonEmptySGPath G
    _∷_∣_∣_ : ∀ i (p : NonEmptySGPath G) → i ∉ₙₑₚ p → (i , source p) ᵉ∈ᵍ G → NonEmptySGPath G

  data _∉ₙₑₚ_ {n : ℕ} where
    notThere : ∀ {i j k i≢j e∈G} → k ≢ i → k ≢ j   → k ∉ₙₑₚ i ∺ j ∣ i≢j ∣ e∈G
    notHere  : ∀ {i p k i∉p e∈G} → k ≢ i → k ∉ₙₑₚ p → k ∉ₙₑₚ i ∷ p ∣ i∉p ∣ e∈G

  source (i ∺ _ ∣ _ ∣ _) = i
  source (i ∷ _ ∣ _ ∣ _) = i


  _∉ₙₑₚ?_ : ∀ {G} → Decidable (_∉ₙₑₚ_ {G})
  k ∉ₙₑₚ? (i ∺ j ∣ _ ∣ _) with k ≟ i | k ≟ j 
  ... | yes k≡i | _       = no λ{(notThere k≢i _) → k≢i k≡i}
  ... | _       | yes k≡j = no λ{(notThere _ k≢j) → k≢j k≡j}
  ... | no  k≢i | no  k≢j = yes (notThere k≢i k≢j)
  k ∉ₙₑₚ? (i ∷ p ∣ _ ∣ _) with k ≟ i | k ∉ₙₑₚ? p
  ... | yes i≡j | _       = no λ{(notHere i≢j _) → i≢j i≡j }
  ... | _       | no  i∈p = no λ{(notHere _ i∉p) → i∈p i∉p}
  ... | no  i≢j | yes i∉p = yes (notHere i≢j i∉p)


  -- Equality

  data _≈ₙₑₚ_ {G} : Rel (NonEmptySGPath G) a where
    _∺_ : ∀ {i j k l i≢j k≢l ij∈G kl∈G} → i ≡ k → j ≡ l   → i ∺ j ∣ i≢j ∣ ij∈G ≈ₙₑₚ k ∺ l ∣ k≢l ∣ kl∈G
    _∷_ : ∀ {i k p q i∉p k∉q ip∈G kq∈G} → i ≡ k → p ≈ₙₑₚ q → i ∷ p ∣ i∉p ∣ ip∈G ≈ₙₑₚ k ∷ q ∣ k∉q ∣ kq∈G



  data _≤ₙₑₚ_ {G} : Rel (NonEmptySGPath G) a where
    stopFirst   : ∀ {i j k l i≢j k≢l ij∈G kl∈G} → i ≡ k → j ≤ l → i ∺ j ∣ i≢j ∣ ij∈G ≤ₙₑₚ k ∺ l ∣ k≢l ∣ kl∈G
    stopSecond  : ∀ {i j k l i≢j k≢l ij∈G kl∈G} → i < k → i ∺ j ∣ i≢j ∣ ij∈G ≤ₙₑₚ k ∺ l ∣ k≢l ∣ kl∈G
    stepUnequal : ∀ {i j p q i∉p j∉q ip∈G jq∈G} → i < j → i ∷ p ∣ i∉p ∣ ip∈G ≤ₙₑₚ j ∷ q ∣ j∉q ∣ jq∈G
    stepEqual   : ∀ {i j p q i∉p j∉q ip∈G jq∈G} → i ≡ j → p ≤ₙₑₚ q → i ∷ p ∣ i∉p ∣ ip∈G ≤ₙₑₚ j ∷ q ∣ j∉q ∣ jq∈G



  -- Operations

  destination : ∀ {G} → NonEmptySGPath G → Fin n
  destination (_ ∺ j ∣ _ ∣ _) = j
  destination (_ ∷ p ∣ _ ∣ _) = destination p

  length : ∀ {G} → NonEmptySGPath G → ℕ
  length (_ ∺ _ ∣ _ ∣ _) = 1
  length (_ ∷ p ∣ _ ∣ _) = suc (length p)





  ---------------
  -- All paths --
  ---------------

  infix 4 _∉_ _≈ₚ_ _≉ₚ_

  data SGPath G : Set a where
    [] : SGPath G
    [_] : NonEmptySGPath G → SGPath G

  data _∉_ {G} : Fin n → SGPath G → Set a where
    notHere : ∀ {i} → i ∉ []
    notThere : ∀ {i p} → i ∉ₙₑₚ p → i ∉ [ p ]

  _∈_ : ∀ {G} → Fin n → SGPath G → Set a
  i ∈ p = ¬ (i ∉ p)

  _∉?_ : ∀ {n} → Decidable (_∉_ {n})
  k ∉? []    = yes notHere
  k ∉? [ p ] with k ∉ₙₑₚ? p
  ... | yes k∉p = yes (notThere k∉p)
  ... | no  k∈p = no λ{(notThere k∉p) → k∈p k∉p}

  -- Equality

  data _≈ₚ_ {G} : Rel (SGPath G) a where
    [] : [] ≈ₚ []
    [_] : ∀ {p q} → p ≈ₙₑₚ q → [ p ] ≈ₚ [ q ]

  _≉ₚ_ : ∀ {n} → Rel (SGPath n) a
  xs ≉ₚ ys = ¬ (xs ≈ₚ ys)

  -- Orderings

  infix 4 _≤ₚ_ _≰ₚ_

  data _≤ₚ_ {G} : Rel (SGPath G) a where
    stop : ∀ {p} → [] ≤ₚ p
    len  : ∀ {p} {q} → length p <ℕ length q → [ p ] ≤ₚ [ q ]
    lex  : ∀ {p} {q} → length p ≡ length q → p ≤ₙₑₚ q → [ p ] ≤ₚ [ q ]

  _≰ₚ_ : ∀ {n} → Rel (SGPath n) a
  p ≰ₚ q = ¬ (p ≤ₚ q)


  weight : ∀ {b} {B : Set b} → (A → B → B) → B → ∀ {G : Graph A n} → SGPath G → B
  weight _▷_ 1# [] = 1#
  weight _▷_ 1# [ _ ∺ _ ∣ _ ∣ (v , _) ] = v ▷ 1#
  weight _▷_ 1# [ _ ∷ p ∣ _ ∣ (v , _) ] = v ▷ weight _▷_ 1# [ p ]


  ---------------
  -- All paths --
  ---------------

  tryLength2 : ∀ G → List (Fin n × Fin n) → List (NonEmptySGPath G)
  tryLength2 G [] = []
  tryLength2 G ((i , j) ∷ xs) with i ≟ j | (i , j) ᵉ∈ᵍ? G
  ... | yes _  | _        = tryLength2 G xs
  ... | _      | no  _    = tryLength2 G xs
  ... | no i≢j | yes ij∈G = i ∺ j ∣ i≢j ∣ ij∈G ∷ tryLength2 G xs

  extendAll : ∀ {G} → List (NonEmptySGPath G) → Fin n → List (NonEmptySGPath G)
  extendAll {_} []       _ = []
  extendAll {G} (p ∷ ps) i with i ∉ₙₑₚ? p | (i , source p) ᵉ∈ᵍ? G
  ... | no  _   | _        = extendAll ps i
  ... | _       | no  _    = extendAll ps i
  ... | yes i∉p | yes ip∈G = i ∷ p ∣ i∉p ∣ ip∈G ∷ extendAll ps i

  allPathsOfLength : ∀ G → ℕ → List (NonEmptySGPath G)
  allPathsOfLength G 0       = []
  allPathsOfLength G 1       = tryLength2 G (combine _,_ (allFin n) (allFin n))
  allPathsOfLength G (suc l) = concat (map (extendAll (allPathsOfLength G l)) (allFin n))

  allNEPaths : ∀ G → List (NonEmptySGPath G)
  allNEPaths G = concat (map (allPathsOfLength G ∘ toℕ)(allFin n))

  allSGPaths : ∀ G → List (SGPath G)
  allSGPaths G = [] ∷ map [_] (allNEPaths G)
