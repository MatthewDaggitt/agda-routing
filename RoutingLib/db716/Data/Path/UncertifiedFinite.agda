open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Nat using (ℕ; suc)
open import Data.Fin using (Fin; inject₁; _≟_)
open import Data.List using (List; []; _∷_; _++_; foldl; foldr; map)
open import Data.List.Any using (Any)
open import Data.List.All using (All)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Binary using (Rel)
open import Algebra using (Semiring)
open import Level using () renaming (zero to ℓ₀)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)
open import RoutingLib.Data.Matrix.Relation.Equality using (_≈ₘ_)


module RoutingLib.db716.Data.Path.UncertifiedFinite where

Vertex : ℕ → Set 
Vertex n = Fin n

Edge : ℕ → Set
Edge n = Vertex n × Vertex n

Path : ℕ → Set
Path n = List (Edge n)

infix 4 _∈ₑ_ _∈ₚ_ _∉ₚ_

data _∈ₑ_ : ∀ {n} → Vertex n → Edge n → Set where
  left : ∀ {n} {i j : Fin n} → i ∈ₑ (i , j)
  right : ∀ {n} {i j : Fin n} → j ∈ₑ (i , j)

_∈ₚ_ : ∀ {n} → Vertex n → Path n → Set
i ∈ₚ p = Any (i ∈ₑ_) p

_∉ₚ_ : ∀ {n} → Vertex n → Path n → Set
i ∉ₚ p = ¬ (i ∈ₚ p)

infix 4 _⇿_

data _⇿_ : ∀ {n} → Edge n → Path n → Set where
  start : ∀ {n} {i j : Fin n} → (i , j) ⇿ []
  continue : ∀ {n} {i j k : Fin n} {p : Path n} → (i , j) ⇿ (j , k) ∷ p

infix 4 _≈ₚ_ _≉ₚ_

{-
data _≈ₚ_ : ∀ {n} → Rel (Path n) ℓ₀ where
  []≈ₚ[] : ∀ {n} → _≈ₚ_ {n} [] []
  x∷xs≈ₚy∷ys : {! !}
-}

_≈ₚ_ : ∀ {n} → Rel (Path n) ℓ₀
_≈ₚ_ {n} = _≡_

_≉ₚ_ : ∀ {n} → Rel (Path n) ℓ₀
p ≉ₚ q = ¬ (p ≈ₚ q)

length : ∀ {n} → Path n → ℕ
length [] = 0
length (_ ∷ p) = suc (length p)

module _ {c ℓ} (S : Semiring c ℓ) where
  open import RoutingLib.Data.Matrix
  open import RoutingLib.db716.Algebra.SemiringMatrix S
  open Semiring S
  open import Relation.Binary.EqReasoning setoid

  weight : ∀ {n} → SquareMatrix Carrier n → Path n → Carrier
  weight M [] = 1#
  weight M ((i , j) ∷ p) = M i j * weight M p

  private pow : ∀ {n} → SquareMatrix Carrier n → ℕ → SquareMatrix Carrier n
  pow {n} M ℕ.zero = 𝟙
  pow M (suc k) = M ⊗ (pow M k)

  allFins : ∀ n → List (Fin n)
  allFins ℕ.zero = []
  allFins (suc n) = Fin.zero ∷ (Data.List.map Fin.suc (allFins n))

  all-k-length-paths-from-to : ∀ n → ℕ → (Vertex n) → (Vertex n) → List (Path n)
  all-k-length-paths-to : ∀ n → ℕ → (Vertex n) → List (Path n)

  all-k-length-paths-from-to n ℕ.zero u v with (u ≟ v)
  ... | (yes _) = [] ∷ []
  ... | (no _) = []
  all-k-length-paths-from-to ℕ.zero (suc k) u v = Data.List.map (λ [] → (u , v) ∷ []) (all-k-length-paths-to ℕ.zero k v)
  all-k-length-paths-from-to (suc n) (suc k) u v = Data.List.map (λ {[] → (u , v) ∷ [] ; ((w , t) ∷ p) → (u , w) ∷ (w , t) ∷ p} ) (all-k-length-paths-to (suc n) k v)

  all-k-length-paths-to 0 k ()
  all-k-length-paths-to (suc n) ℕ.zero v = []
  all-k-length-paths-to (suc n) (suc k) v = foldl _++_ [] (Data.List.map (λ u → all-k-length-paths-from-to (suc n) (suc k) u v) (allFins (suc n)))

  -- Assumes _+_ "selects" the best weight from two paths
  -- Can maybe find a better name for this because in some cases (eg flow problems) _+_ does not have to be selective
  best-path-weight : ∀ {n} → SquareMatrix Carrier n → List (Path n) → Carrier
  best-path-weight M l = foldr (λ p x → weight M p + x) 0# l

  mat-pows-find-best-paths : (n k : ℕ) → (i j : Fin n) → (M : SquareMatrix Carrier n) → pow M k i j ≈ best-path-weight M (all-k-length-paths-from-to n k i j)
  mat-pows-find-best-paths 0 _ ()
  mat-pows-find-best-paths (suc n) ℕ.zero i j M with i ≟ j
  ... | yes i≡j = sym (+-identityʳ 1#)
  ... | no i≢j = refl
  mat-pows-find-best-paths (suc n) (suc k) i j M = sym (begin
    foldr (λ p x → weight M p + x) 0# (all-k-length-paths-from-to (suc n) (suc k) i j)
      ≈⟨ {!!} ⟩
    pow M (suc k) i j ∎
    )

  
