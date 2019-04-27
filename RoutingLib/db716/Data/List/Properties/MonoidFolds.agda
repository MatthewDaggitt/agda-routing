open import Algebra using (Monoid)

module RoutingLib.db716.Data.List.Properties.MonoidFolds {c ℓ} (M : Monoid c ℓ) where
  open Monoid M renaming (Carrier to C)

  open import Data.List

  foldr' = foldr _∙_ ε
  
  foldr-++-commute : ∀ (xs ys : List C) → foldr' (xs ++ ys) ≈ foldr' xs ∙ foldr' ys
  foldr-++-commute [] ys = sym (identityˡ _)
  foldr-++-commute (x ∷ xs) ys = trans (∙-cong refl (foldr-++-commute xs ys)) (sym (assoc x (foldr' xs) (foldr' ys)))

  foldr-map : ∀ {a} {A : Set a} (xs : List A) (f : A → C) → foldr (λ x y → f x ∙ y) ε xs ≈ foldr' (map f xs)
  foldr-map [] f = refl
  foldr-map (x ∷ xs) f = ∙-cong refl (foldr-map xs f)

{-
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

-}
