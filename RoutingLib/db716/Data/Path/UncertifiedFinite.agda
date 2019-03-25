open import Data.Product using (_×_; _,_; <_,_>; proj₁; proj₂)
open import Data.Nat using (ℕ; suc) renaming (_*_ to _×ₙ_)
open import Data.Fin using (Fin; inject₁; _≟_)
open import Data.List using (List; []; _∷_; _++_; foldl; foldr; map; concat)
open import Data.List.Any using (Any)
open import Data.List.All using (All; []; _∷_; tabulate)
open import Data.List.Properties
open import Data.List.Relation.Pointwise using (Pointwise) renaming (refl to ≈ₚ-refl)
open import Function using (_∘_)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Unary using (Pred)
open import Relation.Binary using (Rel)
open import Algebra using (Semiring)
open import Level using () renaming (zero to ℓ₀)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; cong₂) renaming (refl to ≡-refl; cong to ≡-cong; sym to ≡-sym)
open import RoutingLib.Data.Matrix.Relation.Equality using (_≈ₘ_)



module RoutingLib.db716.Data.Path.UncertifiedFinite where

Vertex : ℕ → Set 
Vertex n = Fin n

Edge : ℕ → Set
Edge n = Vertex n × Vertex n

Path : ℕ → Set
Path n = List (Edge n)

{-
data Edge : ∀ n → Fin n → Fin n → Set where
  (_,_) : ∀ {n} → (i j : Fin n) → Edge n i j

data Path : ∀ n → Fin n → Fin n → Set where
  [] : ∀ {i j} → Path 0 i j
  _∷_ : ∀ {n} {i j k : Fin n} → Edge n i j → Path n j k → Path n i k
-}

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

_≈ₚ_ : ∀ {n} → Rel (Path n) ℓ₀
_≈ₚ_ {n} = Pointwise _≡_

_≉ₚ_ : ∀ {n} → Rel (Path n) ℓ₀
p ≉ₚ q = ¬ (p ≈ₚ q)

length : ∀ {n} → Path n → ℕ
length [] = 0
length (_ ∷ p) = suc (length p)

module _ {c ℓ} (S : Semiring c ℓ) where
  open import RoutingLib.Data.Matrix using (SquareMatrix) renaming (map to matmap)
  open import RoutingLib.db716.Algebra.SemiringMatrix S
  open import RoutingLib.db716.Algebra.Properties.Summation S
  open import RoutingLib.db716.Data.Matrix
  open import RoutingLib.Data.Table using () renaming (foldr to tfoldr)
  open Semiring S

  weight : ∀ {n} → SquareMatrix Carrier n → Path n → Carrier
  weight M [] = 1#
  weight M ((i , j) ∷ p) = M i j * weight M p

  private pow : ∀ {n} → SquareMatrix Carrier n → ℕ → SquareMatrix Carrier n
  pow {n} M ℕ.zero = 𝟙
  pow M 1 = M
  pow M (suc (suc k)) = M ⊗ (pow M (suc k))

  allFins : ∀ n → List (Fin n)
  allFins ℕ.zero = []
  allFins (suc n) = Fin.zero ∷ (Data.List.map Fin.suc (allFins n))

  addVertex : ∀ {n} → Fin n → Path n → Path n
  addVertex {n} v [] = (v , v) ∷ []
  addVertex {n} v ((w , t) ∷ p) = (v , w) ∷ (w , t) ∷ p

  data StartsWith : ∀ {n} → Path n → Fin n → Set where
    startsWith : ∀ {n} (p : Path n) (i : Fin n) {j : Fin n} → StartsWith ((i , j) ∷ p) i

  _▻_ = addVertex

  _▻*_ : ∀ {n} → Fin n → List (Path n) → List (Path n)
  i ▻* l = map (i ▻_) l

  all-k-length-paths-from-to : ∀ n → ℕ → (Vertex n) → (Vertex n) → List (Path n)
  all-k-length-paths-to : ∀ n → ℕ → (Vertex n) → List (Path n)

  all-k-length-paths-from-to ℕ.zero k ()
  all-k-length-paths-from-to (suc n) ℕ.zero u v with (u ≟ v)
  ... | (yes _) = [] ∷ []
  ... | (no _) = []
  all-k-length-paths-from-to (suc n) (suc 0) u v = ((u , v) ∷ []) ∷ []
  all-k-length-paths-from-to (suc n) (suc (suc k)) u v = Data.List.map (addVertex u) (all-k-length-paths-to (suc n) (suc k) v)

  all-all-k-length-paths-from-to : ∀ n → ℕ → Fin n → List (List (Path n))
  all-all-k-length-paths-from-to ℕ.zero k ()
  --all-all-k-length-paths-from-to (suc n) 0 v = ([] ∷ []) ∷ []
  all-all-k-length-paths-from-to (suc n) k v = Data.List.map (λ u → all-k-length-paths-from-to (suc n) k u v) (allFins (suc n))

  all-k-length-paths-to 0 k ()
  all-k-length-paths-to (suc n) k v = foldr _++_ [] (all-all-k-length-paths-from-to (suc n) k v)

  -- Assumes _+_ "selects" the best weight from two paths
  -- Can maybe find a better name for this because in some cases (eg flow problems) _+_ does not have to be selective
  best-path-weight : ∀ {n} → SquareMatrix Carrier n → List (Path n) → Carrier
  best-path-weight M l = foldr (λ p x → weight M p + x) 0# l

  accum : List Carrier → Carrier
  accum = foldr _+_ 0#

  accumFunc : ∀ {a} {A : Set a} → List A → (A → Carrier) → Carrier
  accumFunc l f = foldr (λ a x → (f a) + x) 0# l

  module mat-powers-thm where

    addVertex-weights-lemma : ∀ {n} {i j : Fin n} {p : Path n} {M : SquareMatrix Carrier n} → StartsWith p j → M i j * weight M p ≈ weight M (addVertex i p)
    addVertex-weights-lemma {n} {i} {j} {((j , _) ∷ p)} {M} (startsWith p j) = refl

    folds-lemma1' : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} (g : A → B) (f : B → C → C) (c₀ : C) (ps : List A) →
      foldr (f ∘ g) c₀ ps ≡ foldr f c₀ (map g ps)
    folds-lemma1' g f c₀ [] = ≡-refl
    folds-lemma1' g f c₀ (x ∷ ps) = cong₂ f ≡-refl (folds-lemma1' g f c₀ ps)

    folds-lemma1 : ∀ {a b} {A : Set a} {B : Set b} (g : A → B) (f : B → Carrier → Carrier) (c₀ : Carrier) (ps : List A) →
      foldr (f ∘ g) c₀ ps ≈ foldr f c₀ (map g ps)
    folds-lemma1 g f c₀ ps = reflexive (folds-lemma1' g f c₀ ps)

    foldr→map : ∀ {a} {A : Set a} (f : A → Carrier) (as : List A) → accumFunc as f ≈ accum (map f as)
    foldr→map f [] = refl
    foldr→map f (a ∷ as) = +-cong refl (foldr→map f as)

    folds-lemma2' : (l1 l2 : List Carrier) → accum l1 + accum l2 ≈ accum (l1 ++ l2)
    folds-lemma2' [] l2 = +-identityˡ _
    folds-lemma2' (x ∷ l1) l2 = begin
      x + accum l1 + accum l2
        ≈⟨ +-assoc x _ _ ⟩
      x + (accum l1 + accum l2)
        ≈⟨ +-cong refl (folds-lemma2' l1 l2) ⟩
      x + (accum (l1 ++ l2)) ∎
      where open import Relation.Binary.EqReasoning setoid

  
    folds-lemma2 : ∀ (n : ℕ) (μ : Path n → Carrier) (l1 l2 : List (Path n)) →
      (accumFunc l1 μ) + (accumFunc l2 μ) ≈ (accumFunc (l1 ++ l2) μ)
    folds-lemma2 n μ [] l2 = +-identityˡ _
    folds-lemma2 n μ (x ∷ l1) l2 = begin
      μ x + (accumFunc l1 μ) + (accumFunc l2 μ)
        ≈⟨ +-assoc (μ x) _ _ ⟩
      μ x + ((accumFunc l1 μ) + (accumFunc l2 μ))
        ≈⟨ +-cong refl (folds-lemma2 n μ l1 l2) ⟩
      μ x + accumFunc (l1 ++ l2) μ ∎
      where open import Relation.Binary.EqReasoning setoid

    map-distr-++ˡ : ∀ {a b} {A : Set a} {B : Set b} (f : A → B) (xs ys : List A) → map f (xs ++ ys) ≡ (map f xs) ++ (map f ys)
    map-distr-++ˡ f [] ys = ≡-refl
    map-distr-++ˡ f (x ∷ xs) ys = ≡-cong (f x ∷_) (map-distr-++ˡ f xs ys)

    folds-lemma3 : ∀ (n : ℕ) (i : Fin n) (μ : Path n → Carrier) (l1 l2 : List (Path n)) →
      accumFunc (i ▻* l1) μ + accumFunc (i ▻* l2) μ ≈ accumFunc (i ▻* (l1 ++ l2)) μ
    folds-lemma3 ℕ.zero ()
    folds-lemma3 (suc n) i μ l1 l2 = begin
      accumFunc (i ▻* l1) μ + accumFunc (i ▻* l2) μ
        ≈⟨ folds-lemma2 (suc n) μ (i ▻* l1) (i ▻* l2) ⟩
      accumFunc ((i ▻* l1) ++ (i ▻* l2)) μ
        ≡⟨ ≡-cong (foldr (λ p → μ p +_) 0#) (≡-sym (map-distr-++ˡ (i ▻_) l1 l2)) ⟩
      accumFunc (i ▻* (l1 ++ l2)) μ ∎
      where open import Relation.Binary.EqReasoning setoid

    folds-lemma4 : ∀ (n : ℕ) (pathWeights : Fin n → List Carrier) →
      ∑ (λ k → accum (pathWeights k)) ≈ accum (concat (map pathWeights (allFins n)))
    folds-lemma4 ℕ.zero pathWeights = refl
    folds-lemma4 (suc n) pathWeights = begin
      accum (pathWeights Fin.zero) + ∑ (λ k → accum (pathWeights (Fin.suc k)))
        ≡⟨⟩
      accum (pathWeights Fin.zero) + ∑ (λ k → accum ((pathWeights ∘ Fin.suc) k))
        ≈⟨ +-cong refl (folds-lemma4 n (pathWeights ∘ Fin.suc)) ⟩
      accum (pathWeights Fin.zero) + accum (concat (map (pathWeights ∘ Fin.suc) (allFins n)))
        ≈⟨ +-cong refl (reflexive (≡-cong accum (≡-cong concat (map-compose (allFins n))))) ⟩
      accum (pathWeights Fin.zero) + accum (concat (map pathWeights (map Fin.suc (allFins n))))
        ≈⟨ folds-lemma2' ((pathWeights Fin.zero)) (concat (map pathWeights (map Fin.suc (allFins n)))) ⟩
      accum (pathWeights Fin.zero ++ concat (map pathWeights (map Fin.suc (allFins n)))) ∎
      where open import Relation.Binary.EqReasoning setoid

    folds-lemma : ∀ (n : ℕ) (i : Fin n) (μ : Path n → Carrier) (pathsFrom : Fin n → (List (Path n))) →
      ∑ (λ k → accumFunc (pathsFrom k) (μ ∘ (i ▻_))) ≈ accumFunc (i ▻* (concat (map pathsFrom (allFins n)))) μ

    folds-lemma ℕ.zero ()
    folds-lemma (suc n) i μ pathsFrom = begin
      ∑ (λ k → foldr (λ p x → (μ (i ▻ p)) + x) 0# (pathsFrom k))
        ≈⟨ ∑-cong (λ k → folds-lemma1 (λ p → μ (i ▻ p)) _+_ 0# (pathsFrom k)) ⟩
      ∑ (λ k → accum (map (μ ∘ (i ▻_)) (pathsFrom k)))
        ≡⟨⟩
      ∑ (λ k → accum (((map (μ ∘ (i ▻_))) ∘ pathsFrom) k))
        ≈⟨ folds-lemma4 (suc n) ((map (μ ∘ (i ▻_))) ∘ pathsFrom) ⟩
      accum (concat (map ((map (μ ∘ (i ▻_))) ∘ pathsFrom) (allFins (suc n))))
        ≡⟨ ≡-cong (accum ∘ concat) (map-compose {_} {_} {_} {_} {_} {_} {map (μ ∘ (i ▻_))} {pathsFrom} (allFins (suc n))) ⟩
      accum (concat (map (map (μ ∘ (i ▻_))) (map pathsFrom (allFins (suc n)))))
        ≡⟨ ≡-cong accum (concat-map (map pathsFrom (allFins (suc n)))) ⟩
      accum (map (μ ∘ (i ▻_)) (concat (map pathsFrom (allFins (suc n)))))
        ≡⟨ ≡-cong accum (map-compose (concat (map pathsFrom (allFins (suc n))))) ⟩
      accum (map μ (map (i ▻_) (concat (map pathsFrom (allFins (suc n))))))
        ≡⟨⟩
      accum (map μ (i ▻* (concat (map pathsFrom (allFins (suc n))))))
        ≈⟨ sym (folds-lemma1 μ _+_ 0# (i ▻* (concat (map pathsFrom (allFins (suc n)))))) ⟩
      foldr (λ p x → (μ p) + x) 0# (i ▻* (concat (map pathsFrom (allFins (suc n))))) ∎
      where open import Relation.Binary.EqReasoning setoid

    path-accum-distr : ∀ (n : ℕ) (y : Carrier) (M : SquareMatrix Carrier n) (ps : List (Path n)) → y * (accumFunc ps (weight M)) ≈ accumFunc ps (λ p → y * weight M p)
    path-accum-distr n y M [] = zeroʳ y
    path-accum-distr n y M (x ∷ ps) = begin
      y * (weight M x + accumFunc ps (weight M))
        ≈⟨ distribˡ y _ _ ⟩
      y * (weight M x) + y * (accumFunc ps (weight M))
        ≈⟨ +-cong refl (path-accum-distr n y M ps) ⟩
      y * (weight M x) + (accumFunc ps (λ p → y * weight M p)) ∎ 
      where open import Relation.Binary.EqReasoning setoid

    accumFunc-cong : ∀ {a} {A : Set a} {f g : A → Carrier} → (l : List A) → (All (λ x → f x ≈ g x) l) → accumFunc l f ≈ accumFunc l g
    accumFunc-cong {a} {A} {f} {g} [] f≈g = refl
    accumFunc-cong {a} {A} {f} {g} (x ∷ l) (fx≈gx ∷ f≈g) = +-cong fx≈gx (accumFunc-cong l f≈g)

    list-lemma : ∀ {a b p} {A : Set a} {B : Set b} (P : Pred B p) (xs : List A) (f : A → B) → All (P ∘ f) xs → All P (map f xs)
    list-lemma P [] f p = []
    list-lemma P (x ∷ xs) f (px ∷ pxs) = px ∷ list-lemma P xs f pxs

    startsWith-lemma : ∀ {n} (i : Vertex n) (p : Path n) → StartsWith (i ▻ p) i
    startsWith-lemma i [] = startsWith [] i
    startsWith-lemma i ((j , k) ∷ p) = startsWith ((j , k) ∷ p) i

    addVertex-lemma1 : ∀ n (i l : Vertex n) (x : Path n) (M : SquareMatrix Carrier n) → M i l * weight M (l ▻ x) ≈ weight M (i ▻ (l ▻ x))
    addVertex-lemma1 ℕ.zero ()
    addVertex-lemma1 (suc n) i l x M = addVertex-weights-lemma (startsWith-lemma l x)

    paths-lemma : ∀ n k (i l j : Vertex (suc n)) (M : SquareMatrix Carrier (suc n)) →
      All (λ x → M i l * weight M x ≈ weight M (addVertex i x)) (all-k-length-paths-from-to (suc n) (suc k) l j)
    paths-lemma n 0 i l j M = refl ∷ []
    paths-lemma n (suc k) i l j M = list-lemma ((λ x → M i l * weight M x ≈ weight M (addVertex i x))) ((all-k-length-paths-to (suc n) (suc k) j)) (l ▻_)
      (tabulate (λ {x} _ → addVertex-lemma1 (suc n) i l x M))

    folds-lemma6 : ∀ (n k : ℕ) (i l j : Fin n) (M : SquareMatrix Carrier n) →
      accumFunc (all-k-length-paths-from-to n (suc k) l j) (λ p → M i l * (weight M p)) ≈ accumFunc (all-k-length-paths-from-to n (suc k) l j) (λ p → weight M (i ▻ p))
    folds-lemma6 0 _ ()
    folds-lemma6 (suc n) k i l j M = accumFunc-cong (all-k-length-paths-from-to (suc n) (suc k) l j) (paths-lemma n k i l j M)

    mat-pows-find-best-paths : (n k : ℕ) → (i j : Fin n) → (M : SquareMatrix Carrier n) → pow M k i j ≈ best-path-weight M (all-k-length-paths-from-to n k i j)
    mat-pows-find-best-paths 0 _ ()
    mat-pows-find-best-paths (suc n) ℕ.zero i j M with i ≟ j
    ... | yes i≡j = sym (+-identityʳ 1#)
    ... | no i≢j = refl
    mat-pows-find-best-paths (suc n) (suc 0) i j M = sym (trans (+-identityʳ _) (*-identityʳ (M i j)))
    mat-pows-find-best-paths (suc n) (suc (suc k)) i j M = begin
      pow M (suc (suc k)) i j
        ≡⟨⟩
      ∑ (λ l → (M i l * (pow M (suc k)) l j))
        ≈⟨  ∑-cong {suc n} {λ l → M i l * (pow M (suc k)) l j} {_} (λ l → *-cong refl (mat-pows-find-best-paths (suc n) (suc k) l j M)) ⟩
      ∑ (λ l → M i l * best-path-weight M (all-k-length-paths-from-to (suc n) (suc k) l j))
        ≡⟨⟩
      ∑ (λ l → M i l * (accumFunc (all-k-length-paths-from-to (suc n) (suc k) l j) (weight M)))
        ≈⟨ ∑-cong (λ l → path-accum-distr (suc n) (M i l) M (all-k-length-paths-from-to (suc n) (suc k) l j)) ⟩
      ∑ (λ l → accumFunc (all-k-length-paths-from-to (suc n) (suc k) l j) (λ p → M i l * (weight M p)))
        ≈⟨ ∑-cong {_} {λ l → accumFunc (all-k-length-paths-from-to (suc n) (suc k) l j) (λ p → weight M ((i , l) ∷ p))} (λ l → folds-lemma6 (suc n) k i l j M) ⟩
      ∑ (λ l → accumFunc (all-k-length-paths-from-to (suc n) (suc k) l j) (λ p → weight M (i ▻ p)))
        ≈⟨ folds-lemma (suc n) i (weight M) (λ m → all-k-length-paths-from-to (suc n) (suc k) m j) ⟩
      accumFunc (map (i ▻_) (concat (map (λ u → all-k-length-paths-from-to (suc n) (suc k) u j) (allFins (suc n))))) (weight M)
        ≡⟨⟩
      best-path-weight M (all-k-length-paths-from-to (suc n) (suc (suc k)) i j) ∎
      where open import Relation.Binary.EqReasoning setoid

  module mat-power-sums-thm where
    powSum : ∀ {n} → SquareMatrix Carrier n → ℕ → SquareMatrix Carrier n
    powSum M ℕ.zero = 𝟙
    powSum M (suc k) = powSum M k ⊕ pow M (suc k)

    all-≤k-length-paths-from-to : ∀ n → ℕ → Vertex n → Vertex n → List (Path n)
    all-≤k-length-paths-from-to n 0 i j with i ≟ j
    ... | yes i≡j = [] ∷ []
    ... | no i≢j = []
    all-≤k-length-paths-from-to n (suc k) i j = all-≤k-length-paths-from-to n k i j ++ all-k-length-paths-from-to n (suc k) i j

    mat-pow-sums-find-best-paths : ∀ n k (i j : Vertex n) (M : SquareMatrix Carrier n) → powSum M k i j ≈ best-path-weight M (all-≤k-length-paths-from-to n k i j)
    mat-pow-sums-find-best-paths n ℕ.zero i j M with i ≟ j
    ... | yes i≡j = sym (+-identityʳ 1#)
    ... | no i≢j = refl
    mat-pow-sums-find-best-paths n (suc k) i j M = begin
      powSum M (suc k) i j
        ≡⟨⟩
      powSum M k i j + pow M (suc k) i j
        ≈⟨ +-cong (mat-pow-sums-find-best-paths n k i j M) (mat-powers-thm.mat-pows-find-best-paths n (suc k) i j M) ⟩
      best-path-weight M (all-≤k-length-paths-from-to n k i j) + best-path-weight M (all-k-length-paths-from-to n (suc k) i j)
        ≈⟨ mat-powers-thm.folds-lemma2 n (weight M) (all-≤k-length-paths-from-to n k i j) (all-k-length-paths-from-to n (suc k) i j) ⟩
      best-path-weight M (all-≤k-length-paths-from-to n k i j ++ all-k-length-paths-from-to n (suc k) i j)
        ≡⟨⟩
      best-path-weight M (all-≤k-length-paths-from-to n (suc k) i j) ∎
      where open import Relation.Binary.EqReasoning setoid

