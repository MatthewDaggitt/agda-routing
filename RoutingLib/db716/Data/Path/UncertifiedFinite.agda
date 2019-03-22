open import Data.Product using (_×_; _,_; <_,_>; proj₁; proj₂)
open import Data.Nat using (ℕ; suc) renaming (_*_ to _×ₙ_)
open import Data.Fin using (Fin; inject₁; _≟_)
open import Data.List using (List; []; _∷_; _++_; foldl; foldr; map; concat)
open import Data.List.Any using (Any)
open import Data.List.All using (All)
open import Data.List.Properties
open import Function using (_∘_)
open import Relation.Nullary using (¬_; yes; no)
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
  open import RoutingLib.Data.Matrix renaming (map to matmap)
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
  pow M (suc k) = M ⊗ (pow M k)

  allFins : ∀ n → List (Fin n)
  allFins ℕ.zero = []
  allFins (suc n) = Fin.zero ∷ (Data.List.map Fin.suc (allFins n))

  addVertex : ∀ {n} → Fin n → Path n → Path n
  addVertex {n} v [] = (v , v) ∷ []
  addVertex {n} v ((w , t) ∷ p) = (v , w) ∷ (w , t) ∷ p

  _▻_ = addVertex

  _▻*_ : ∀ {n} → Fin n → List (Path n) → List (Path n)
  i ▻* l = map (i ▻_) l

  all-k-length-paths-from-to : ∀ n → ℕ → (Vertex n) → (Vertex n) → List (Path n)
  all-k-length-paths-to : ∀ n → ℕ → (Vertex n) → List (Path n)

  all-k-length-paths-from-to n ℕ.zero u v with (u ≟ v)
  ... | (yes _) = [] ∷ []
  ... | (no _) = []
  all-k-length-paths-from-to ℕ.zero (suc k) ()
  all-k-length-paths-from-to (suc n) (suc k) u v = Data.List.map (addVertex u) (all-k-length-paths-to (suc n) k v)

  all-all-k-length-paths-from-to : ∀ n → ℕ → Fin n → List (List (Path n))
  all-all-k-length-paths-from-to ℕ.zero k ()
  all-all-k-length-paths-from-to (suc n) k v = Data.List.map (λ u → all-k-length-paths-from-to (suc n) k u v) (allFins (suc n))

  all-k-length-paths-to 0 k ()
  --all-k-length-paths-to (suc n) ℕ.zero v = []
  all-k-length-paths-to (suc n) k v = foldr _++_ [] (all-all-k-length-paths-from-to (suc n) k v) --(Data.List.map (λ u → all-k-length-paths-from-to (suc n) (suc k) u v) (allFins (suc n)))
  
  -- Assumes _+_ "selects" the best weight from two paths
  -- Can maybe find a better name for this because in some cases (eg flow problems) _+_ does not have to be selective
  best-path-weight : ∀ {n} → SquareMatrix Carrier n → List (Path n) → Carrier
  best-path-weight M l = foldr (λ p x → weight M p + x) 0# l

  flatten : ∀ {a} {A : Set a} → List (List A) → List A
  flatten = foldr _++_ []

  folds-lemma1' : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} (g : A → B) (f : B → C → C) (c₀ : C) (ps : List A) →
    foldr (f ∘ g) c₀ ps ≡ foldr f c₀ (map g ps)
  folds-lemma1' g f c₀ [] = ≡-refl
  folds-lemma1' g f c₀ (x ∷ ps) = cong₂ f ≡-refl (folds-lemma1' g f c₀ ps)

  folds-lemma1 : ∀ {a b} {A : Set a} {B : Set b} (g : A → B) (f : B → Carrier → Carrier) (c₀ : Carrier) (ps : List A) →
    foldr (f ∘ g) c₀ ps ≈ foldr f c₀ (map g ps)
  folds-lemma1 g f c₀ ps = reflexive (folds-lemma1' g f c₀ ps)

  {-paths-via : Fin n → Carrier
  paths-via k = foldr (λ p x → (μ p) + x) 0# (i ▻* (pathsFrom k))-}

  {-
  folds-lemma2' : ∀ {a} {A : Set a} (n : ℕ) (f : A → Carrier → Carrier) (l : List A) →
    foldr f 0# l ≡ foldr f 0# (l ++ [])

  folds-lemma2' n μ l = foldr-cong {!!} ≡-refl {!!}
  

  folds-lemma2 : ∀ (n : ℕ) (μ : Path n → Carrier) (l1 l2 : List (Path n)) →
    (foldr (λ p x → (μ p) + x) 0# l1) + (foldr (λ p x → (μ p) + x) 0# l2) ≈ (foldr (λ p x → (μ p) + x) 0# (l1 ++ l2))

  folds-lemma2 n μ l1 [] = begin
    (foldr (λ p → (μ p) +_) 0# l1) + 0#
      ≈⟨ +-identityʳ _ ⟩
    foldr (λ p → (μ p) +_) 0# l1
      ≈⟨ {!!} ⟩
    foldr (λ p → (μ p) +_) 0# (l1 ++ []) ∎
  folds-lemma2 n μ l1 (x ∷ l2) = {!!}
  -}

  accum : List Carrier → Carrier
  accum = foldr _+_ 0#

  foldr→map : ∀ {a} {A : Set a} (f : A → Carrier) (as : List A) → foldr (λ a x → (f a) + x) 0# as ≈ accum (map f as)
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
    (foldr (λ p x → (μ p) + x) 0# l1) + (foldr (λ p x → (μ p) + x) 0# l2) ≈ (foldr (λ p x → (μ p) + x) 0# (l1 ++ l2))
  folds-lemma2 n μ [] l2 = +-identityˡ _
  folds-lemma2 n μ (x ∷ l1) l2 = begin
    μ x + (foldr (λ p → (μ p) +_) 0# l1) + (foldr (λ p → (μ p) +_) 0# l2)
      ≈⟨ +-assoc (μ x) _ _ ⟩
    μ x + ((foldr (λ p → (μ p) +_) 0# l1) + (foldr (λ p → (μ p) +_) 0# l2))
      ≈⟨ +-cong refl (folds-lemma2 n μ l1 l2) ⟩
    μ x + foldr (λ p → (μ p) +_) 0# (l1 ++ l2) ∎
    where open import Relation.Binary.EqReasoning setoid

  map-distr-++ˡ : ∀ {a b} {A : Set a} {B : Set b} (f : A → B) (xs ys : List A) → map f (xs ++ ys) ≡ (map f xs) ++ (map f ys)
  map-distr-++ˡ f [] ys = ≡-refl
  map-distr-++ˡ f (x ∷ xs) ys = ≡-cong (f x ∷_) (map-distr-++ˡ f xs ys)

  folds-lemma3 : ∀ (n : ℕ) (i : Fin n) (μ : Path n → Carrier) (l1 l2 : List (Path n)) →
    foldr (λ p x → (μ p) + x) 0# (i ▻* l1) + foldr (λ p x → (μ p) + x) 0# (i ▻* l2) ≈ foldr (λ p x → (μ p) + x) 0# (i ▻* (l1 ++ l2))
  folds-lemma3 ℕ.zero ()
  folds-lemma3 (suc n) i μ l1 l2 = begin
    foldr (λ p → (μ p) +_) 0# (i ▻* l1) + (foldr (λ p → (μ p) +_) 0# (i ▻* l2))
      ≈⟨ folds-lemma2 (suc n) μ (i ▻* l1) (i ▻* l2) ⟩
    foldr (λ p → (μ p) +_) 0# ((i ▻* l1) ++ (i ▻* l2))
      ≡⟨ ≡-cong (foldr (λ p → μ p +_) 0#) (≡-sym (map-distr-++ˡ (i ▻_) l1 l2)) ⟩
    foldr (λ p → (μ p) +_) 0# (i ▻* (l1 ++ l2)) ∎
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

{-
  folds-lemma4 : ∀ (n : ℕ) (i : Fin n) (μ : Path n → Carrier) (pathsFrom : Fin n → List (Path n)) →
    ∑ (λ k → foldr (λ p → μ p +_) 0# (i ▻* (pathsFrom k))) ≈ foldr (λ p → μ p +_) 0# (i ▻* (concat (map pathsFrom (allFins n))))
  folds-lemma4 ℕ.zero ()
  folds-lemma4 (suc n) i μ pathsFrom = begin
    ∑ (λ k → foldr (λ p → μ p +_) 0# (i ▻* (pathsFrom k)))
      ≈⟨ +-cong refl {!(folds-lemma4 (suc n) i μ (pathsFrom ∘ Fin.suc)))!} ⟩
    foldr (λ p x → μ p + x) 0# (i ▻* (pathsFrom Fin.zero)) + foldr (λ p x → μ p + x) 0# (i ▻* (concat (map (pathsFrom ∘ Fin.suc) (allFins n))))
      ≈⟨ {!!} ⟩
    foldr (λ p x → μ p + x) 0# (i ▻* (concat (map pathsFrom (allFins (suc n))))) ∎
    where open import Relation.Binary.EqReasoning setoid
-}
  -- WTS : ∑ (λ x → foldr (λ p → μ p +_) 0# (i ▻* (pathsFrom (Fin.suc x)))) ≈ foldr (λ p → μ p +_) 0# (i ▻* (foldr _++_ [] (map (λ x → pathsFrom (Fin.suc x)) (allFins n))))


  folds-lemma : ∀ (n : ℕ) (i : Fin n) (μ : Path n → Carrier) (pathsFrom : Fin n → (List (Path n))) →
    ∑ (λ k → foldr (λ p → (μ (i ▻ p)) +_) 0# (pathsFrom k)) ≈ foldr (λ p x → (μ p) + x) 0# (i ▻* (concat (map pathsFrom (allFins n))))


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

  path-accum-distr : ∀ (n : ℕ) (y : Carrier) (M : SquareMatrix Carrier n) (ps : List (Path n)) → y * (foldr (λ p x → (weight M p) + x) 0# ps) ≈ foldr (λ p x → y * (weight M p) + x) 0# ps
  path-accum-distr n y M [] = zeroʳ y
  path-accum-distr n y M (x ∷ ps) = begin
    y * (weight M x + foldr (λ p → _+_ (weight M p)) 0# ps)
      ≈⟨ distribˡ y _ _ ⟩
    y * (weight M x) + y * (foldr (λ p → _+_ (weight M p)) 0# ps)
      ≈⟨ +-cong refl (path-accum-distr n y M ps) ⟩
    y * (weight M x) + foldr (λ p → _+_ (y * weight M p)) 0# ps ∎ 
    where open import Relation.Binary.EqReasoning setoid

  folds-lemma6 : ∀ (n k : ℕ) (i l j : Fin n) (M : SquareMatrix Carrier n) →
    foldr (λ p x → (weight M ((i , l) ∷ p)) + x) 0# (all-k-length-paths-from-to n k l j) ≈ foldr (λ p x → (weight M (addVertex i p)) + x) 0# (all-k-length-paths-from-to n k l j)
  folds-lemma6 n ℕ.zero i l j M = ?
  folds-lemma6 n (suc k) i l j M = ?

  mat-pows-find-best-paths : (n k : ℕ) → (i j : Fin n) → (M : SquareMatrix Carrier n) → pow M k i j ≈ best-path-weight M (all-k-length-paths-from-to n k i j)
  mat-pows-find-best-paths 0 _ ()
  mat-pows-find-best-paths (suc n) ℕ.zero i j M with i ≟ j
  ... | yes i≡j = sym (+-identityʳ 1#)
  ... | no i≢j = refl
  mat-pows-find-best-paths (suc n) (suc k) i j M = begin
    pow M (suc k) i j
      ≡⟨⟩
    ∑ (λ l → (M i l * (pow M k) l j))
      ≈⟨  ∑-cong {suc n} {λ l → M i l * (pow M k) l j} {_} (λ l → *-cong refl (mat-pows-find-best-paths (suc n) k l j M)) ⟩
    ∑ (λ l → (M i l * best-path-weight M (all-k-length-paths-from-to (suc n) k l j)))
      ≡⟨⟩
    ∑ (λ l → (M i l * (foldr (λ p x → (weight M p) + x) 0# (all-k-length-paths-from-to (suc n) k l j))))
      ≈⟨ ∑-cong (λ l → path-accum-distr (suc n) (M i l) M (all-k-length-paths-from-to (suc n) k l j)) ⟩
    ∑ (λ l → (foldr (λ p x → M i l * (weight M p) + x) 0# (all-k-length-paths-from-to (suc n) k l j)))
      ≡⟨⟩
    ∑ (λ l → (foldr (λ p x → (weight M ((i , l) ∷ p)) + x) 0# (all-k-length-paths-from-to (suc n) k l j)))
      ≈⟨ {!!} ⟩
    ∑ (λ l → (foldr (λ p x → (weight M (addVertex i p)) + x) 0# (all-k-length-paths-from-to (suc n) k l j)))
      ≈⟨ folds-lemma (suc n) i (weight M) (λ m → all-k-length-paths-from-to (suc n) k m j) ⟩
    foldr (λ p x → (weight M p) + x) 0# (Data.List.map (addVertex i) (foldr _++_ [] (Data.List.map (λ u → all-k-length-paths-from-to (suc n) k u j) (allFins (suc n)))))
      ≡⟨⟩
    best-path-weight M (Data.List.map (addVertex i) (foldr _++_ [] (all-all-k-length-paths-from-to (suc n) k j)))
      ≡⟨⟩
    best-path-weight M (Data.List.map (addVertex i) (all-k-length-paths-to (suc n) k j))
      ≡⟨⟩
    best-path-weight M (all-k-length-paths-from-to (suc n) (suc k) i j)
      ≡⟨⟩
    best-path-weight M (all-k-length-paths-from-to (suc n) (suc k) i j) ∎
    where open import Relation.Binary.EqReasoning setoid
  
{-
tfoldr : ∀ {a b} {A : Set a} {B : Set b} →
        (A → B → B) → B → ∀ {n} → Table A n → B
tfoldr f e {zero}  t = e
tfoldr f e {suc n} t = f (t zero) (tfoldr f e (t ∘ suc))

foldr : ∀ {a b} {A : Set a} {B : Set b} → (A → B → B) → B → List A → B
foldr c n []       = n
foldr c n (x ∷ xs) = c x (foldr c n xs)

-}
