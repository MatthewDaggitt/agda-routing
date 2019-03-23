open import Agda.Builtin.Equality using (_≡_; refl)

open import Algebra using (Semiring)
open import Algebra.FunctionProperties
open import Algebra.Structures
open import Data.Fin using (Fin; suc; zero; _≟_) renaming (_≤_ to _F≤_)
open import Data.Nat using (ℕ; suc; zero; _≤_; _<_)
open import Data.Product using (_,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (sym; cong; trans; _≢_)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Negation using (contradiction)

open import RoutingLib.Data.Matrix
open import RoutingLib.Data.Table

open import RoutingLib.db716.Data.Matrix
open import RoutingLib.db716.Data.Table

module RoutingLib.db716.Algebra.SemiringMatrix {c ℓ} (S : Semiring c ℓ ) where

open Semiring S renaming (Carrier to C; refl to ≈-refl; sym to ≈-sym; trans to ≈-trans; setoid to ≈-setoid)

open import RoutingLib.db716.Algebra.Properties.Summation S
open import Relation.Binary.EqReasoning ≈-setoid
open import RoutingLib.Data.Matrix.Relation.Binary.Equality ≈-setoid

private Mat : (n : ℕ) → Set _
Mat n = SquareMatrix C n

private Vec : (n : ℕ) → Set _
Vec = Table C

-- Define operators for elementwise and scalar multiplication for vectors for convenience.
private _⊛_ : {n : ℕ} → Vec n → Vec n → Vec n
_⊛_ u v = λ i → u i * v i

-- Standard dot product on vectors
_∙_ : {n : ℕ} → Vec n → Vec n → C
_∙_ u v = ∑ (λ i → u i *  v i)

-- Matrix addition and multiplication:

infixl 6 _⊕_
infixl 7 _⊗_

_⊕_ : {n : ℕ} → Mat n → Mat n → Mat n
(A ⊕ B) i j = (A i j) + (B i j)

_⊗_ : {n : ℕ} → Mat n → Mat n → Mat n
(A ⊗ B) i j = (row i A) ∙ (col j B)

-- Additive and multiplictive identity matrices

𝟘 : {n : ℕ} → Mat n
𝟘 _ _ = 0#

𝟙 : {n : ℕ} → Mat n
𝟙 i j with i ≟ j
... | yes _ = 1#
... | no _ = 0#

private 0ᵥ : {n : ℕ} → Vec n
0ᵥ _ = 0#

private 0ᶠ : ∀ {n} → Fin (suc n)
0ᶠ = Fin.zero

-- Various lemmas for vectors (Tables) over semirings

0∙v≈0 : {n : ℕ} → ∀ (v : Vec n) → 0ᵥ ∙ v ≈ 0#
0∙v≈0 v = ∑0≈0 (0ᵥ ⊛ v) (λ i → zeroˡ (v i))

v∙0≈0 : {n : ℕ} → ∀ (v : Vec n) → v ∙ 0ᵥ ≈ 0#
v∙0≈0 v = ∑0≈0 (v ⊛ 0ᵥ) (λ i → zeroʳ (v i))

𝟙₍ᵢ₊₁₎₍ⱼ₊₁₎≈𝟙ᵢⱼ : {n : ℕ} → ∀ i j → (𝟙 {suc n} (suc i) (suc j)) ≈ (𝟙 {n} i j)
𝟙₍ᵢ₊₁₎₍ⱼ₊₁₎≈𝟙ᵢⱼ i j with i ≟ j
... | yes i≡j =  ≈-refl
... | no i≢j = ≈-refl

∙-cong : {n : ℕ} {u v w x : Vec n} → (∀ i → u i ≈ v i) → (∀ j → w j ≈ x j) →  u ∙ w ≈ v ∙ x
∙-cong eq1 eq2 = ∑-cong (λ i → *-cong (eq1 i) (eq2 i))

∙-distˡ : {n : ℕ} (u v : Vec n) (c : C) → c * (u ∙ v) ≈ (λ i → c * u i) ∙ v
∙-distˡ u v c = ≈-trans (∑-distˡ (u ⊛ v) c) ((∑-cong (λ i → ≈-sym (*-assoc c (u i) (v i)))))

∙-distʳ : {n : ℕ} (u v : Vec n) (c : C) → (u ∙ v) * c ≈ u ∙ (λ i → v i * c)
∙-distʳ u v c = ≈-trans (∑-distʳ (u ⊛ v) c) ((∑-cong (λ i → *-assoc (u i) (v i) c)))

𝟙ᵢ∙v≈vᵢ : ∀ {n} i v → (𝟙 {n} i) ∙ v ≈ v i
𝟙ᵢ∙v≈vᵢ {zero} ()
𝟙ᵢ∙v≈vᵢ {suc n} zero v = begin
  1# * (v 0ᶠ) + 0ᵥ ∙ (tail v)
    ≈⟨ +-cong (*-identityˡ (v 0ᶠ)) (0∙v≈0 (tail v)) ⟩
  v 0ᶠ + 0#
    ≈⟨ +-identityʳ (v 0ᶠ) ⟩
  v 0ᶠ                        ∎
𝟙ᵢ∙v≈vᵢ {suc n} (suc i) v =  begin
  0# * (v 0ᶠ) + (tail (𝟙 {suc n} (suc i)) ∙ tail v)
    ≈⟨ +-cong (zeroˡ (v 0ᶠ)) ≈-refl ⟩
  0# + tail (𝟙 {suc n} (suc i)) ∙ tail v
    ≈⟨ +-identityˡ _ ⟩
  tail (𝟙 {suc n} (suc i)) ∙ (tail v)
    ≈⟨ ∙-cong (𝟙₍ᵢ₊₁₎₍ⱼ₊₁₎≈𝟙ᵢⱼ i) (λ j → ≈-refl) ⟩
  𝟙 i ∙ tail v
    ≈⟨ 𝟙ᵢ∙v≈vᵢ i (tail v) ⟩
  v (suc i)                                                ∎

v∙𝟙ᵢ≈vᵢ : ∀ {n} i v → v ∙ (𝟙 {n} i) ≈ v i
v∙𝟙ᵢ≈vᵢ {zero} ()
v∙𝟙ᵢ≈vᵢ {n} zero v = begin
  (v 0ᶠ) * 1# + (tail v) ∙ 0ᵥ
    ≈⟨ +-cong (*-identityʳ (v 0ᶠ)) (v∙0≈0 (tail v)) ⟩
  (v 0ᶠ) + 0#
    ≈⟨ +-identityʳ (v 0ᶠ) ⟩
  v 0ᶠ ∎
v∙𝟙ᵢ≈vᵢ {suc n} (suc i) v = begin
  (v 0ᶠ) * 0# + (tail v) ∙ (tail (𝟙 {suc n} (suc i)))
    ≈⟨ +-cong (zeroʳ (v 0ᶠ)) ≈-refl ⟩
  0# + (tail v) ∙ (tail (𝟙 {suc n} (suc i)))
    ≈⟨ +-identityˡ _ ⟩
  (tail v) ∙ (tail (𝟙 {suc n} (suc i)))
    ≈⟨ ∙-cong (λ j → ≈-refl) (𝟙₍ᵢ₊₁₎₍ⱼ₊₁₎≈𝟙ᵢⱼ i) ⟩
  (tail v) ∙ (𝟙 i)
    ≈⟨ v∙𝟙ᵢ≈vᵢ i (tail v) ⟩
  v (suc i) ∎

𝟙ᵀ≈𝟙 : ∀ {n : ℕ} → ((𝟙 {n}) ᵀ) ≈ₘ 𝟙 {n}
𝟙ᵀ≈𝟙 i j with i ≟ j | j ≟ i
... | yes _ | yes _ = ≈-refl
... | yes i≡j | no j≢i = contradiction (sym i≡j) j≢i
... | no i≢j | yes j≡i = contradiction (sym j≡i) i≢j
... | no _ | no _ = ≈-refl

-- Proofs for semiring properties:

⊕-cong : (n : ℕ) → Congruent₂ (_≈ₘ_ {n}) _⊕_
⊕-cong n {x} {y} {z} {w} x≈y z≈w i j = +-cong (x≈y i j) (z≈w i j)

⊗-cong : (n : ℕ) → Congruent₂ (_≈ₘ_ {n}) _⊗_
⊗-cong n {x} {y} {z} {w} x≈y z≈w i j = ∑-cong (λ k → *-cong (x≈y i k) (z≈w k j))

⊕-assoc : (n : ℕ) → Associative (_≈ₘ_ {n}) _⊕_
⊕-assoc n x y z i j = +-assoc (x i j) (y i j) (z i j)

⊗-assoc : (n : ℕ) → Associative (_≈ₘ_ {n}) _⊗_
⊗-assoc n x y z i j = begin
  ((x ⊗ y) ⊗ z) i j
    ≈⟨ ∑-cong (λ k → ∑-distʳ (λ l → x i l * y l k) (z k j)) ⟩
  ∑ (λ k → ∑ (λ l → (x i l * y l k) * z k j))
    ≈⟨ ∑-cong (λ k → (∑-cong (λ l → *-assoc (x i l) (y l k) (z k j)))) ⟩
  ∑ (λ k → ∑ (λ l → x i l * (y l k * z k j)))
    ≈⟨ ∑-comm (λ k l → x i l * (y l k * z k j)) ⟩
  ∑ (λ l → ∑ (λ k → x i l * (y l k * z k j)))
    ≈⟨ ∑-cong (λ l → ≈-sym (∑-distˡ (λ k → y l k * z k j) (x i l)))  ⟩
  (x ⊗ (y ⊗ z)) i j ∎

⊕-comm : (n : ℕ) → Commutative (_≈ₘ_ {n}) _⊕_
⊕-comm n x y i j = +-comm (x i j) (y i j)

mat-distribˡ : (n : ℕ) → _DistributesOverˡ_ (_≈ₘ_ {n}) _⊗_ _⊕_
mat-distribˡ n x y z i j = ≈-trans (∑-cong (λ k → distribˡ (x i k) (y k j) (z k j)))
                                   (≈-sym (∑-reassoc (λ k → x i k * y k j) (λ k → x i k * z k j)))

mat-distribʳ : (n : ℕ) → _DistributesOverʳ_ (_≈ₘ_ {n}) _⊗_ _⊕_
mat-distribʳ n x y z i j = ≈-trans (∑-cong (λ k → distribʳ (x k j) (y i k) (z i k)))
                                   (≈-sym (∑-reassoc (λ k → y i k * x k j) (λ k → z i k * x k j)))

mat-distrib : (n : ℕ) → _DistributesOver_ (_≈ₘ_ {n}) _⊗_ _⊕_
mat-distrib n = mat-distribˡ n , mat-distribʳ n

⊕-identityˡ : (n : ℕ) → LeftIdentity _≈ₘ_ (𝟘 {n}) _⊕_
⊕-identityˡ n A i j = +-identityˡ _

⊕-identityʳ : (n : ℕ) → RightIdentity _≈ₘ_ (𝟘 {n}) _⊕_
⊕-identityʳ n A i j = +-identityʳ _

⊕-identity : (n : ℕ) → Identity _≈ₘ_ (𝟘 {n}) _⊕_
⊕-identity n = ⊕-identityˡ n , ⊕-identityʳ n

⊗-identityˡ : (n : ℕ) → LeftIdentity _≈ₘ_ (𝟙 {n}) _⊗_
⊗-identityˡ n A i j = 𝟙ᵢ∙v≈vᵢ i (col j A)

⊗-identityʳ : (n : ℕ) → RightIdentity _≈ₘ_ (𝟙 {n}) _⊗_
⊗-identityʳ n A i j = begin
  (row i A) ∙ (col j 𝟙) ≈⟨  ∙-cong (λ k → ≈-refl) (𝟙ᵀ≈𝟙 j)  ⟩
  (row i A) ∙ (row j 𝟙) ≈⟨ v∙𝟙ᵢ≈vᵢ j (row i A) ⟩
  A i j ∎

⊗-identity : (n : ℕ) → Identity _≈ₘ_ 𝟙 _⊗_
⊗-identity n = ⊗-identityˡ n , ⊗-identityʳ n

mat-zeroˡ : (n : ℕ) → LeftZero (_≈ₘ_ {n}) 𝟘 _⊗_
mat-zeroˡ n x i j = ∑0*v≈0 (col j x)

mat-zeroʳ : (n : ℕ) → RightZero (_≈ₘ_ {n}) 𝟘 _⊗_
mat-zeroʳ n x i j = ∑v*0≈0 (x i)

mat-zero : (n : ℕ) → Zero (_≈ₘ_ {n}) 𝟘 _⊗_
mat-zero n = (mat-zeroˡ n , mat-zeroʳ n)

-- Packaging the properties up as as an IsSemiring

⊗-isSemigroup : (n : ℕ) → IsSemigroup (_≈ₘ_ {n}) _⊗_
⊗-isSemigroup n = record
  { isEquivalence = ≈ₘ-isEquivalence
  ; assoc = ⊗-assoc n
  ; ∙-cong = ⊗-cong n
  }

⊕-isSemigroup : (n : ℕ) → IsSemigroup (_≈ₘ_ {n}) _⊕_
⊕-isSemigroup n = record
  { isEquivalence = ≈ₘ-isEquivalence
  ; assoc = ⊕-assoc n
  ; ∙-cong = ⊕-cong n
  }

⊗-isMonoid : (n : ℕ) → IsMonoid _≈ₘ_ _⊗_ 𝟙
⊗-isMonoid n = record
  { isSemigroup = ⊗-isSemigroup n
  ; identity = ⊗-identity n
  }

⊕-isCommutativeMonoid : (n : ℕ) → IsCommutativeMonoid _≈ₘ_ _⊕_ 𝟘
⊕-isCommutativeMonoid n = record
  { isSemigroup = ⊕-isSemigroup n
  ; identityˡ = ⊕-identityˡ n
  ; comm = ⊕-comm n
  }

mat-isSemiringWithoutAnnihilatingZero : (n : ℕ) → IsSemiringWithoutAnnihilatingZero _≈ₘ_ _⊕_ _⊗_ 𝟘 𝟙
mat-isSemiringWithoutAnnihilatingZero n = record
  { +-isCommutativeMonoid = ⊕-isCommutativeMonoid n
  ; *-isMonoid = ⊗-isMonoid n
  ; distrib = mat-distrib n
  }

mat-isSemiring : (n : ℕ) → IsSemiring _≈ₘ_ _⊕_ _⊗_ 𝟘 𝟙
mat-isSemiring n = record
  { isSemiringWithoutAnnihilatingZero = mat-isSemiringWithoutAnnihilatingZero n
  ; zero = mat-zero n
  }

SemiringMat : ℕ → Semiring _ _
SemiringMat n = record
  { Carrier = Mat n
  ; _≈_ = _≈ₘ_
  ; _+_ = _⊕_
  ; _*_ = _⊗_
  ; 0# = 𝟘
  ; 1# = 𝟙
  ; isSemiring = mat-isSemiring n
  }
