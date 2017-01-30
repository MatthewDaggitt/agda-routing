open import Data.Nat using (ℕ; suc; zero; s≤s; _⊓_) renaming (_≤_ to _≤ℕ_)
open import Data.List using (List; []; _∷_; map; concat; gfilter; foldr)
open import Data.Product using (_,_)
open import Data.Vec using (Vec; []; _∷_; allFin) renaming (toList to toListᵥ)
open import Data.Fin using (Fin; _≤_; toℕ) renaming (zero to fzero; suc to fsuc)
open import Data.Fin.Properties using (_≟_)
open import Data.Maybe using (Maybe; just; nothing)
open import Level using () renaming (zero to lzero)
open import Relation.Binary using (Rel; Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)
open import Relation.Nullary using (¬_; yes; no)

open import RoutingLib.Data.Graph using (Graph; nodes)

module RoutingLib.Data.Graph.EPath where
 
  -- Data types

  data EPath (n : ℕ) : Set lzero
  data _∉_ {n : ℕ} : Fin n → EPath n → Set lzero
  
  data EPath (n : ℕ) where
    [_]   : Fin n → EPath n
    _∷_∣_ : ∀ i (p : EPath n) → i ∉ p → EPath n

  data _∉_ {n : ℕ} where
    notThere : ∀ {i j}       → i ≢ j → i ∉ [ j ]
    notHere  : ∀ {i j p j∉p} → i ≢ j → i ∉ p → i ∉ (j ∷ p ∣ j∉p)

  _∉?_ : ∀ {n} → Decidable (_∉_ {n})
  i ∉? [ j ] with i ≟ j 
  ... | yes i≡j           = no λ{(notThere i≢j) → i≢j i≡j}
  ... | no  i≢j           = yes (notThere i≢j)
  i ∉? (j ∷ p ∣ _) with i ≟ j | i ∉? p
  ... | yes i≡j | _       = no λ{(notHere i≢j _) → i≢j i≡j }
  ... | _       | no  i∈p = no λ{(notHere _ i∉p) → i∈p i∉p}
  ... | no  i≢j | yes i∉p = yes (notHere i≢j i∉p)

  _∈_ : ∀ {n} → Fin n → EPath n → Set lzero
  i ∈ p = ¬ (i ∉ p)

  -- Operations

  length : ∀ {n} → EPath n → ℕ
  length [ _ ] = zero
  length (_ ∷ p ∣ _) = suc (length p)

  source : ∀ {n} → EPath n → Fin n
  source [ i ] = i
  source (i ∷ _ ∣ _) = i

  destination : ∀ {n} → EPath n → Fin n
  destination [ i ] = i
  destination (_ ∷ p ∣ _) = destination p

  toList : ∀ {n} → EPath n → List (Fin n)
  toList [ i ]       = i ∷ []
  toList (i ∷ p ∣ _) = i ∷ toList p

  toVec : ∀ {n} → (p : EPath n) → Vec (Fin n) (suc (length p))
  toVec [ i ]        = i ∷ []
  toVec (i ∷ p ∣ _ ) = i ∷ toVec p
  
  lookup : ∀ {n} → (p : EPath n) → Fin (suc (length p)) → (Fin n)
  lookup p fzero = source p
  lookup [ _ ] (fsuc ())
  lookup (i ∷ p ∣ _ ) (fsuc j) = lookup p j

  extendAll : ∀ {n} → List (EPath n) → Fin n → List (EPath n)
  extendAll []       _ = []
  extendAll (p ∷ ps) i with i ∉? p
  ... | no _    = extendAll ps i
  ... | yes i∉p = (i ∷ p ∣ i∉p) ∷ extendAll ps i

  allPathsOfLength : ∀ {n} → ℕ → List (EPath n)
  allPathsOfLength {n} zero = map [_] (toListᵥ (allFin n))
  allPathsOfLength {n} (suc l) = concat (map (extendAll (allPathsOfLength l)) (toListᵥ (allFin n)))

  allPaths : ∀ {n} → List (EPath n)
  allPaths {n} = concat (map allPathsOfLength (map toℕ (toListᵥ (allFin n)))) 
  
  private

    lookup : ∀ {n} → (p : NonEmptySPath n) → Fin (suc (length p)) → Fin n
    lookup (i ∺ j ∣ _ ∣ _) fzero            = i
    lookup (i ∺ j ∣ _ ∣ _) (fsuc fzero)     = j
    lookup (i ∺ j ∣ _ ∣ _) (fsuc (fsuc ()))
    lookup (i ∷ p ∣ _ ∣ _) fzero            = i
    lookup (i ∷ p ∣ _ ∣ _) (fsuc k)         = lookup p k 
    
    lookup-∈ : ∀ {n} → (p : NonEmptySPath n) → ∀ i {k} → lookup p i ≡ k → k ∈ₙₑₚ p
    lookup-∈ (i ∺ j ∣ _ ∣ _) fzero            refl (notThere i≢i _) = i≢i refl
    lookup-∈ (i ∺ j ∣ _ ∣ _) (fsuc fzero)     refl (notThere _ j≢j) = j≢j refl
    lookup-∈ (i ∺ j ∣ _ ∣ _) (fsuc (fsuc ()))
    lookup-∈ (i ∷ p ∣ _ ∣ _) fzero            refl (notHere i≢i _)  = i≢i refl
    lookup-∈ (i ∷ p ∣ _ ∣ _) (fsuc k)         pᵢ≡k  (notHere _ i∉p)  = lookup-∈ p k pᵢ≡k i∉p

    lookup! : ∀ {n} (p : NonEmptySPath n) {k l} → k ≢ l → lookup p k ≢ lookup p l
    lookup! _                  {fzero}         {fzero}          0≢0 _ = 0≢0 refl
    lookup! (i ∺ j ∣ i≢j ∣ _) {fzero}          {fsuc fzero}     _     = i≢j
    lookup! (i ∺ j ∣ i≢j ∣ _) {fsuc fzero}     {fzero}          _     = i≢j ∘ sym
    lookup! (i ∺ j ∣ x   ∣ _) {_}              {fsuc (fsuc ())} _
    lookup! (i ∺ j ∣ x   ∣ _) {fsuc (fsuc ())} {_}
    lookup! (i ∺ j ∣ x   ∣ _) {fsuc fzero}     {fsuc fzero}     1≢1 _ = 1≢1 refl
    lookup! (i ∷ p ∣ i∉p ∣ _) {fzero}          {fsuc j}         i≢j i≡pⱼ = contradiction i∉p (lookup-∈ p j (sym i≡pⱼ))
    lookup! (i ∷ p ∣ i∉p ∣ _) {fsuc k}         {fzero}          i≢j pₖ≡i = contradiction i∉p (lookup-∈ p k pₖ≡i)
    lookup! (i ∷ p ∣ x   ∣ _) {fsuc k}         {fsuc l}         k+1≢l+1 pₖ≡pₗ = lookup! p (k+1≢l+1 ∘ cong fsuc) pₖ≡pₗ

  |p|<n : ∀ {n} (p : NonEmptySPath n) → length p <ℕ n
  |p|<n p with suc (length p) ≤ℕ? n
  ... | yes |p|<n = |p|<n
  ... | no  |p|≮n with pigeonhole (m≰n⇨n<m |p|≮n) (lookup p)
  ...   | i , j , i≢j , pᵢ≡pⱼ = contradiction pᵢ≡pⱼ (lookup! p i≢j)






  -- Equality over paths
 
  infix 4 _≈ₚ_ _≉ₚ_

  data _≈ₚ_ {n : ℕ} : Rel (EPath n) lzero where
    [_] : ∀ {i j} → i ≡ j → [ i ] ≈ₚ [ j ]
    _∷_ : ∀ {i j p q i∉p j∉q} → i ≡ j → p ≈ₚ q → i ∷ p ∣ i∉p ≈ₚ j ∷ q ∣ j∉q

  _≉ₚ_ : ∀ {n} → Rel (EPath n) lzero
  xs ≉ₚ ys = ¬ (xs ≈ₚ ys)



  -- Reverse lexicograph ordering over paths

  infix 4 _≤ₚ_ _≰ₚ_

  data _≤ₚ_ {n : ℕ} : Rel (EPath n) lzero where
    stop        : ∀ {i j} → i ≤ j → [ i ] ≤ₚ [ j ]
    stopLeft    : ∀ {i j q j∉q} → [ i ] ≤ₚ q → [ i ] ≤ₚ j ∷ q ∣ j∉q
    stopRight   : ∀ {i j p i∉p} → p ≉ₚ [ j ] → p ≤ₚ [ j ] → i ∷ p ∣ i∉p ≤ₚ [ j ]
    stepEqual   : ∀ {i j p q i∉p j∉q} → p ≈ₚ q → i ≤ j → i ∷ p ∣ i∉p ≤ₚ j ∷ q ∣ j∉q
    stepUnequal : ∀ {i j p q i∉p j∉q} → p ≉ₚ q → p ≤ₚ q  → i ∷ p ∣ i∉p ≤ₚ j ∷ q ∣ j∉q

  _≰ₚ_ : ∀ {n} → Rel (EPath n) lzero
  p ≰ₚ q = ¬ (p ≤ₚ q)


  -- Length ordering over pathsd

  infix 4 _≤ₗ_ _≰ₗ_
  
  _≤ₗ_ : ∀ {n} → Rel (EPath n) lzero
  p ≤ₗ q = length p ≤ℕ length q

  _≰ₗ_ : ∀ {n} → Rel (EPath n) lzero
  p ≰ₗ q = ¬ (p ≤ₗ q)
