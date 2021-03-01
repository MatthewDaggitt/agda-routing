
open import Algebra using (Semiring)

module RoutingLib.db716.Results.MatrixPowers {c ℓ} (S : Semiring c ℓ) where
  open import Data.Nat using (ℕ; suc)
  open import Data.Fin using (Fin; _≟_)
  open import Data.List using (List; []; _∷_; _++_; foldr; map; concat)
  open import Data.List.Relation.Unary.All using (All; []; _∷_; tabulate)
  open import Data.List.Properties using (map-compose; concat-map)
  open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃₂)
  open import Function using (_∘_)
  open import Relation.Nullary using (yes; no)
  open import Relation.Unary using (Pred)
  open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; cong₂) renaming (refl to ≡-refl; cong to ≡-cong; sym to ≡-sym; trans to ≡-trans)
  open import RoutingLib.Data.Matrix.Relation.Binary.Equality using (_≈ₘ_)


  open Semiring S

  open import Algebra.Properties.CommutativeMonoid.Sum +-commutativeMonoid renaming (sum-cong-≋ to ∑-cong)
  open import RoutingLib.Data.Matrix hiding (All; map)
  open import RoutingLib.Data.Matrix.Algebra.Semiring S
  open import RoutingLib.Algebra.Properties.Semiring.Sum S
  open import RoutingLib.db716.Data.Path.UncertifiedFinite
  open import RoutingLib.db716.Data.Path.UncertifiedFinite.Weights S



  private
    pow : ∀ {n} → SquareMatrix Carrier n → ℕ → SquareMatrix Carrier n
    pow {n} = pow'
      where open import RoutingLib.db716.Algebra.Semiring (⊕-⊗-semiring n) using () renaming (pow to pow')

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
    where open import Relation.Binary.Reasoning.Setoid setoid

  
  folds-lemma2 : ∀ (n : ℕ) (μ : Path n → Carrier) (l1 l2 : List (Path n)) →
    (accumFunc l1 μ) + (accumFunc l2 μ) ≈ (accumFunc (l1 ++ l2) μ)
  folds-lemma2 n μ [] l2 = +-identityˡ _
  folds-lemma2 n μ (x ∷ l1) l2 = begin
    μ x + (accumFunc l1 μ) + (accumFunc l2 μ)
      ≈⟨ +-assoc (μ x) _ _ ⟩
    μ x + ((accumFunc l1 μ) + (accumFunc l2 μ))
      ≈⟨ +-cong refl (folds-lemma2 n μ l1 l2) ⟩
    μ x + accumFunc (l1 ++ l2) μ ∎
    where open import Relation.Binary.Reasoning.Setoid setoid
 
  map-distr-++ˡ : ∀ {a b} {A : Set a} {B : Set b} (f : A → B) (xs ys : List A) → map f (xs ++ ys) ≡ (map f xs) ++ (map f ys)
  map-distr-++ˡ f [] ys = ≡-refl
  map-distr-++ˡ f (x ∷ xs) ys = ≡-cong (f x ∷_) (map-distr-++ˡ f xs ys)

  folds-lemma3 : ∀ (n : ℕ) (i : Fin n) (μ : Path n → Carrier) (l1 l2 : List (Path n)) →
    accumFunc (i ▻* l1) μ + accumFunc (i ▻* l2) μ ≈ accumFunc (i ▻* (l1 ++ l2)) μ
  folds-lemma3 (suc n) i μ l1 l2 = begin
    accumFunc (i ▻* l1) μ + accumFunc (i ▻* l2) μ
      ≈⟨ folds-lemma2 (suc n) μ (i ▻* l1) (i ▻* l2) ⟩
    accumFunc ((i ▻* l1) ++ (i ▻* l2)) μ
      ≡⟨ ≡-cong (foldr (λ p → μ p +_) 0#) (≡-sym (map-distr-++ˡ (i ▻_) l1 l2)) ⟩
    accumFunc (i ▻* (l1 ++ l2)) μ ∎
    where open import Relation.Binary.Reasoning.Setoid setoid

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
    where open import Relation.Binary.Reasoning.Setoid setoid

  folds-lemma : ∀ (n : ℕ) (i : Fin n) (μ : Path n → Carrier) (pathsFrom : Fin n → (List (Path n))) →
    ∑ (λ k → accumFunc (pathsFrom k) (μ ∘ (i ▻_))) ≈ accumFunc (i ▻* (concat (map pathsFrom (allFins n)))) μ

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
      ≈˘⟨ folds-lemma1 μ _+_ 0# (i ▻* (concat (map pathsFrom (allFins (suc n))))) ⟩
    foldr (λ p x → (μ p) + x) 0# (i ▻* (concat (map pathsFrom (allFins (suc n))))) ∎
    where open import Relation.Binary.Reasoning.Setoid setoid

  path-accum-distr : ∀ (n : ℕ) (y : Carrier) (M : SquareMatrix Carrier n) (ps : List (Path n)) → y * (accumFunc ps (weight M)) ≈ accumFunc ps (λ p → y * weight M p)
  path-accum-distr n y M [] = zeroʳ y
  path-accum-distr n y M (x ∷ ps) = begin
    y * (weight M x + accumFunc ps (weight M))
      ≈⟨ distribˡ y _ _ ⟩
    y * (weight M x) + y * (accumFunc ps (weight M))
      ≈⟨ +-cong refl (path-accum-distr n y M ps) ⟩
    y * (weight M x) + (accumFunc ps (λ p → y * weight M p)) ∎ 
    where open import Relation.Binary.Reasoning.Setoid setoid
                                                  
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
  addVertex-lemma1 (suc n) i l x M = addVertex-weights-lemma (startsWith-lemma l x)

  paths-lemma : ∀ n k (i l j : Vertex (suc n)) (M : SquareMatrix Carrier (suc n)) →
    All (λ x → M i l * weight M x ≈ weight M (addVertex i x)) (all-k-length-paths-from-to (suc n) (suc k) l j)
  paths-lemma n 0 i l j M = refl ∷ []
  paths-lemma n (suc k) i l j M = list-lemma ((λ x → M i l * weight M x ≈ weight M (addVertex i x))) ((all-k-length-paths-to (suc n) (suc k) j)) (l ▻_)
    (tabulate (λ {x} _ → addVertex-lemma1 (suc n) i l x M))

  folds-lemma6 : ∀ (n k : ℕ) (i l j : Fin n) (M : SquareMatrix Carrier n) →
    accumFunc (all-k-length-paths-from-to n (suc k) l j) (λ p → M i l * (weight M p)) ≈ accumFunc (all-k-length-paths-from-to n (suc k) l j) (λ p → weight M (i ▻ p))
  folds-lemma6 (suc n) k i l j M = accumFunc-cong (all-k-length-paths-from-to (suc n) (suc k) l j) (paths-lemma n k i l j M)

  mat-pows-find-best-paths : (n k : ℕ) → (i j : Fin n) → (M : SquareMatrix Carrier n) → pow M k i j ≈ best-path-weight M (all-k-length-paths-from-to n k i j)
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
    where open import Relation.Binary.Reasoning.Setoid setoid
