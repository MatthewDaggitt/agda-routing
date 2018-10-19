open import Data.Fin.Properties using () renaming (_≟_ to _≟𝔽_)
open import Data.Fin.Dec using (¬∀⟶∃¬; all?)
open import Data.List using (List; foldr)
import Data.List.All.Properties as All
open import Data.List.Relation.Pointwise as Pointwise using (Pointwise; []; _∷_)
open import Data.Nat using (_<_)
open import Data.Nat.Properties using (≤-reflexive)
open import Data.Product using (∃; ∃₂; _×_; _,_; proj₁)
open import Data.Sum using (inj₁; inj₂)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Unary using (Decidable)
import Relation.Binary.EqReasoning as EqReasoning
open import Induction.WellFounded using (Acc; acc)
open import Induction.Nat using (<-wellFounded)

open import RoutingLib.Data.List.Properties using (foldr-presᵇ)
open import RoutingLib.Data.Matrix using (SquareMatrix)
open import RoutingLib.Data.Nat.Properties using (module ≤-Reasoning)
open import RoutingLib.Data.Path.CertifiedI
open import RoutingLib.Data.Path.CertifiedI.Properties using (∉ₚ-resp-≈ₚ; ≈ₚ-trans; ≈ₚ-sym; ≈ₚ-reflexive; ℙₛ; _∉ᵥₚ?_; _⇿ᵥ?_)

open import RoutingLib.Routing.Model using (AdjacencyMatrix)
open import RoutingLib.Routing.Algebra
open import RoutingLib.Routing.Algebra.CertifiedPathAlgebra
import RoutingLib.Routing.Algebra.CertifiedPathAlgebra.Properties as PathAlgebraProperties
import RoutingLib.Routing.Algebra.CertifiedPathAlgebra.Consistency as Consistency
import RoutingLib.Routing.BellmanFord.Synchronous as BellmanFord
import RoutingLib.Routing.BellmanFord.Synchronous.DistanceVector.Properties as BellmanFordProperties

module RoutingLib.Routing.BellmanFord.Synchronous.PathVector.Properties
  {a b ℓ n} (algebra : RawRoutingAlgebra a b ℓ)
  (isPathAlgebra : IsCertifiedPathAlgebra algebra n)
  (A : AdjacencyMatrix algebra n)
  where

open RawRoutingAlgebra algebra
open IsCertifiedPathAlgebra isPathAlgebra
open PathAlgebraProperties isPathAlgebra
open Consistency algebra isPathAlgebra A

open BellmanFord algebra A
open BellmanFordProperties algebra isRoutingAlgebra A

------------------------------------------------------------------------------
-- Path properties

abstract

  p[Iᵢᵢ]≈[] : ∀ i → path (I i i) ≈ₚ valid []
  p[Iᵢᵢ]≈[] i = r≈0⇒path[r]≈[] (≈-reflexive (Iᵢᵢ≡0# i))

  p[Iᵢⱼ]≈∅ : ∀ {i j} → j ≢ i → path (I i j) ≈ₚ invalid
  p[Iᵢⱼ]≈∅ j≢i = r≈∞⇒path[r]≈∅ (≈-reflexive (Iᵢⱼ≡∞ j≢i))

  p[Iᵢⱼ]≈[]⇒i≡j : ∀ {i j} → path (I i j) ≈ₚ valid [] → i ≡ j
  p[Iᵢⱼ]≈[]⇒i≡j {i} {j} p[Iᵢⱼ]≈[] with j ≟𝔽 i
  ... | yes refl = refl
  ... | no  _    = contradiction (≈ₚ-trans (≈ₚ-sym (r≈∞⇒path[r]≈∅ ≈-refl)) p[Iᵢⱼ]≈[]) λ()

  k∉p[Iᵢⱼ] : ∀ i j k → k ∉ₚ path (I i j)
  k∉p[Iᵢⱼ] i j k with j ≟𝔽 i
  ... | yes refl = ∉ₚ-resp-≈ₚ (≈ₚ-sym p[0]≈[]) (valid notThere)
  ... | no  j≢i  = ∉ₚ-resp-≈ₚ (≈ₚ-sym p[∞]≈∅) invalid

  p[σXᵢᵢ]≈[] : ∀ X i → path (σ X i i) ≈ₚ valid []
  p[σXᵢᵢ]≈[] X i = ≈ₚ-trans (path-cong (σXᵢᵢ≈Iᵢᵢ X i)) (p[Iᵢᵢ]≈[] i)

  p[σXᵢⱼ]≈[]⇒i≡j : ∀ X i j → path (σ X i j) ≈ₚ valid [] → i ≡ j
  p[σXᵢⱼ]≈[]⇒i≡j X i j p[σXᵢⱼ]≈[] with σXᵢⱼ≈Aᵢₖ▷Xₖⱼ⊎Iᵢⱼ X i j
  ... | inj₂ σXᵢⱼ≈Iᵢⱼ          = p[Iᵢⱼ]≈[]⇒i≡j (≈ₚ-trans (path-cong (≈-sym σXᵢⱼ≈Iᵢⱼ)) p[σXᵢⱼ]≈[])
  ... | inj₁ (k , σXᵢⱼ≈AᵢₖXₖⱼ) with A i k ▷ X k j ≟ ∞
  ...   | yes AᵢₖXₖⱼ≈∞ = contradiction
    (≈ₚ-trans (≈ₚ-trans (≈ₚ-sym (r≈∞⇒path[r]≈∅ AᵢₖXₖⱼ≈∞)) (path-cong (≈-sym σXᵢⱼ≈AᵢₖXₖⱼ))) p[σXᵢⱼ]≈[]) λ()
  ...   | no  AᵢₖXₖⱼ≉∞ with path (X k j) | inspect path (X k j)
  ...       | invalid | [ p[Xₖⱼ]≡∅ ] = contradiction (p[r]≡∅⇒f▷r≈∞ (A i k) p[Xₖⱼ]≡∅) AᵢₖXₖⱼ≉∞
  ...       | valid q | [ p[Xₖⱼ]≡q ] with ≈ₚ-reflexive p[Xₖⱼ]≡q | (i , k) ⇿ᵥ? q | i ∉ᵥₚ? q
  ...         | pᵣ≈q | no ¬ik⇿q | _       = contradiction (path-reject (A i k) pᵣ≈q (inj₁ ¬ik⇿q)) AᵢₖXₖⱼ≉∞
  ...         | pᵣ≈q | _        | no  i∈q = contradiction (path-reject (A i k) pᵣ≈q (inj₂ i∈q))   AᵢₖXₖⱼ≉∞
  ...         | pᵣ≈q | yes ik⇿q | yes i∉q = contradiction (begin
    valid (_ ∷ q ∣ _ ∣ _) ≈⟨ ≈ₚ-sym (path-accept (A i k) pᵣ≈q AᵢₖXₖⱼ≉∞ ik⇿q i∉q) ⟩
    path (A i k ▷ X k j)  ≈⟨ path-cong (≈-sym σXᵢⱼ≈AᵢₖXₖⱼ) ⟩
    path (σ X i j)        ≈⟨ p[σXᵢⱼ]≈[] ⟩
    valid []              ∎) λ {(valid ())}
    where open EqReasoning (ℙₛ n)

  alignPathExtension : ∀ (X : RoutingMatrix) i j k {u v p e⇿p i∉p} →
            path (A i k ▷ X k j) ≈ₚ valid ((u , v) ∷ p ∣ e⇿p ∣ i∉p) →
            i ≡ u × k ≡ v × path (X k j) ≈ₚ valid p
  alignPathExtension X i j k p[AᵢₖXₖⱼ]≈uv∷p with A i k ▷ X k j ≟ ∞
  ...     | yes AᵢₖXₖⱼ≈∞ = contradiction (
    ≈ₚ-trans (≈ₚ-sym p[AᵢₖXₖⱼ]≈uv∷p) (
      ≈ₚ-trans (path-cong AᵢₖXₖⱼ≈∞) p[∞]≈∅)) λ()
  ...     | no  AᵢₖXₖⱼ≉∞ with path (X k j) | inspect path (X k j)
  ...       | invalid | [ p[Xₖⱼ]≡∅ ] = contradiction (p[r]≡∅⇒f▷r≈∞ (A i k) p[Xₖⱼ]≡∅) AᵢₖXₖⱼ≉∞
  ...       | valid q | [ p[Xₖⱼ]≡q ] with ≈ₚ-reflexive p[Xₖⱼ]≡q | (i , k) ⇿ᵥ? q | i ∉ᵥₚ? q
  ...         | pᵣ≈q | no ¬ik⇿q | _       = contradiction (path-reject (A i k) pᵣ≈q (inj₁ ¬ik⇿q)) AᵢₖXₖⱼ≉∞
  ...         | pᵣ≈q | _        | no  i∈q = contradiction (path-reject (A i k) pᵣ≈q (inj₂ i∈q))   AᵢₖXₖⱼ≉∞
  ...         | pᵣ≈q | yes ik⇿q | yes i∉q with
    ≈ₚ-trans (≈ₚ-sym p[AᵢₖXₖⱼ]≈uv∷p)
      (path-accept (A i k) pᵣ≈q AᵢₖXₖⱼ≉∞ ik⇿q i∉q)
  ...           | valid (refl ∷ p≈q) = refl , refl , ≈ₚ-sym (valid p≈q)

  p[σXᵢⱼ]⇒σXᵢⱼ≈AᵢₖXₖⱼ : ∀ X i j {k l p e⇿p i∉p} →
              path (σ X i j) ≈ₚ valid ((l , k) ∷ p ∣ e⇿p ∣ i∉p) →
              i ≡ l × σ X i j ≈ A i k ▷ X k j × path (X k j) ≈ₚ valid p
  p[σXᵢⱼ]⇒σXᵢⱼ≈AᵢₖXₖⱼ X i j p[σXᵢⱼ]≈uv∷p with i ≟𝔽 j
  ... | yes refl = contradiction (≈ₚ-trans (≈ₚ-sym p[σXᵢⱼ]≈uv∷p) (p[σXᵢᵢ]≈[] X j)) λ{(valid ())}
  ... | no  i≢j with σXᵢⱼ≈Aᵢₖ▷Xₖⱼ⊎Iᵢⱼ X i j
  ...   | inj₂ σXᵢⱼ≈Iᵢⱼ           = contradiction (
    ≈ₚ-trans (≈ₚ-sym p[σXᵢⱼ]≈uv∷p) (
      ≈ₚ-trans (path-cong σXᵢⱼ≈Iᵢⱼ) (p[Iᵢⱼ]≈∅ (i≢j ∘ sym)))) λ()
  ...   | inj₁ (m , σXᵢⱼ≈AᵢₘXₘⱼ) with alignPathExtension X i j m
    (≈ₚ-trans (≈ₚ-sym (path-cong σXᵢⱼ≈AᵢₘXₘⱼ)) p[σXᵢⱼ]≈uv∷p)
  ...     | refl , refl , p[Xₖⱼ]≈p = refl , σXᵢⱼ≈AᵢₘXₘⱼ , p[Xₖⱼ]≈p

------------------------------------------------------------------------------
-- Consistency

𝑪ₘ : RoutingMatrix → Set _
𝑪ₘ X = ∀ i j → 𝑪 (X i j)

𝑰ₘ : RoutingMatrix → Set _
𝑰ₘ X = ¬ 𝑪ₘ X

abstract

  𝑪ₘ? : Decidable 𝑪ₘ
  𝑪ₘ? X = all? (λ i → all? (λ j → 𝑪? (X i j)))

  𝑪ₘ-cong : ∀ {X Y} → X ≈ₘ Y → 𝑪ₘ X → 𝑪ₘ Y
  𝑪ₘ-cong X≈Y Xᶜ i j = 𝑪-cong (X≈Y i j) (Xᶜ i j)

  𝑰ₘ-witness : ∀ {X} → 𝑰ₘ X → ∃₂ λ i j → 𝑰 (X i j)
  𝑰ₘ-witness {X} Xⁱ with ¬∀⟶∃¬ n _ (λ i → all? (λ j → 𝑪? (X i j))) Xⁱ
  ... | (j , Xⱼⁱ) = j , (¬∀⟶∃¬ n _ (λ k → 𝑪? (X j k)) Xⱼⁱ)

  𝑪𝑰⇒≉ₘ : ∀ {X Y} → 𝑪ₘ X → 𝑰ₘ Y → X ≉ₘ Y
  𝑪𝑰⇒≉ₘ Xᶜ Yⁱ X≈Y with 𝑰ₘ-witness Yⁱ
  ... | i , j , Yᵢⱼⁱ = 𝑪𝑰⇒≉ (Xᶜ i j) Yᵢⱼⁱ (X≈Y i j)

  -- Consistency is preserved by ⊕ and ▷

  Iᶜ : 𝑪ₘ I
  Iᶜ i j with j ≟𝔽 i
  ... | yes _ = 0ᶜ
  ... | no  _ = ∞ᶜ

  σ-pres-𝑪ₘ : ∀ {X} → 𝑪ₘ X → 𝑪ₘ (σ X)
  σ-pres-𝑪ₘ Xᶜ i j = foldr-presᵇ {P = 𝑪} ⊕-pres-𝑪
    (Iᶜ i j) (All.tabulate⁺ (λ k → ▷-pres-𝑪 i k (Xᶜ k j)))

  σXᵢⱼⁱ≈Aᵢₖ▷Xₖⱼ : ∀ X i j → 𝑰 (σ X i j) → ∃ λ k → σ X i j ≈ A i k ▷ X k j × 𝑰 (X k j)
  σXᵢⱼⁱ≈Aᵢₖ▷Xₖⱼ X i j σXᵢⱼⁱ with σXᵢⱼ≈Aᵢₖ▷Xₖⱼ⊎Iᵢⱼ X i j
  ... | inj₁ (k , σXᵢⱼ≈Aᵢₖ▷Xₖⱼ) = k , σXᵢⱼ≈Aᵢₖ▷Xₖⱼ , ▷-forces-𝑰 (𝑰-cong σXᵢⱼ≈Aᵢₖ▷Xₖⱼ σXᵢⱼⁱ)
  ... | inj₂ σXᵢⱼ≈Iᵢⱼ           = contradiction (𝑪-cong (≈-sym σXᵢⱼ≈Iᵢⱼ) (Iᶜ i j)) σXᵢⱼⁱ

  σXᵢⱼⁱ⇒Xₖⱼⁱ≉σXₖⱼ : ∀ X i j → 𝑰 (σ X i j) → ∃ λ k → X k j ≉ σ X k j × 𝑰 (X k j)
  σXᵢⱼⁱ⇒Xₖⱼⁱ≉σXₖⱼ X i j σXᵢⱼⁱ = reduction i σXᵢⱼⁱ (<-wellFounded (size (σ X i j)))
    where
    open ≤-Reasoning
    reduction : ∀ l → 𝑰 (σ X l j) → Acc _<_ (size (σ X l j)) →
                ∃ λ k → X k j ≉ σ X k j × 𝑰 (X k j)
    reduction l σXₗⱼⁱ (acc rec) with σXᵢⱼⁱ≈Aᵢₖ▷Xₖⱼ X _ _ σXₗⱼⁱ
    ... | (k , σXₗⱼ≈AₗₖXₖⱼ , Xₖⱼⁱ) with X k j ≟ σ X k j
    ...   | no  Xₖⱼ≉σXₖⱼ = k , Xₖⱼ≉σXₖⱼ , Xₖⱼⁱ
    ...   | yes Xₖⱼ≈σXₖⱼ = reduction k (𝑰-cong Xₖⱼ≈σXₖⱼ Xₖⱼⁱ) (rec (size (σ X k j)) (begin
      size (σ X k j)         ≡⟨ size-cong (≈-sym Xₖⱼ≈σXₖⱼ) ⟩
      size (X k j)           <⟨ ≤-reflexive (sizeⁱ-incr (𝑰-cong σXₗⱼ≈AₗₖXₖⱼ σXₗⱼⁱ)) ⟩
      size (A l k ▷ X k j)   ≡⟨ size-cong (≈-sym σXₗⱼ≈AₗₖXₖⱼ) ⟩
      size (σ X l j)         ∎))

  fixedPointᶜ : ∀ {X} → σ X ≈ₘ X → 𝑪ₘ X
  fixedPointᶜ {X} σX≈X with 𝑪ₘ? (σ X)
  ... | yes σXᶜ = 𝑪ₘ-cong σX≈X σXᶜ
  ... | no  σXⁱ with 𝑰ₘ-witness σXⁱ
  ...   | i , j , σXᵢⱼⁱ with σXᵢⱼⁱ⇒Xₖⱼⁱ≉σXₖⱼ X _ _ σXᵢⱼⁱ
  ...     | k , Xₖⱼ≉σXₖⱼ , _ = contradiction (≈-sym (σX≈X k j)) Xₖⱼ≉σXₖⱼ


------------------------------------------------------------------------------
-- Consistent algebra properties

open BellmanFord algebraᶜ Aᶜ using () renaming
  ( RoutingMatrix to CMatrix
  ; _≈ₘ_ to _≈ᶜₘ_
  ; I    to Ic
  ; σ    to σᶜ
  )

toCMatrix : ∀ {X} → 𝑪ₘ X → CMatrix
toCMatrix {X} Xᶜ i j = X i j , Xᶜ i j

toCMatrix-cong : ∀ {X Y} (Xᶜ : 𝑪ₘ X) (Yᶜ : 𝑪ₘ Y) → X ≈ₘ Y →
                 toCMatrix Xᶜ ≈ᶜₘ toCMatrix Yᶜ
toCMatrix-cong _ _ X≈Y i j = X≈Y i j

I≈toCI : ∀ i j → toCRoute (Iᶜ i j) ≈ᶜ Ic i j
I≈toCI i j with j ≟𝔽 i
... | yes _ = ≈-refl
... | no  _ = ≈-refl

foldrᶜ-lemma : ∀ {e xs} {ys : List CRoute} → 𝑪 e →
                 Pointwise (λ x y → x ≈ proj₁ y) xs ys →
                 𝑪 (foldr _⊕_ e xs)
foldrᶜ-lemma eᶜ []            = eᶜ
foldrᶜ-lemma eᶜ (_∷_ {y = y , yᶜ} x≈y xs≈ys) =
  ⊕-pres-𝑪 (𝑪-cong (≈-sym x≈y) yᶜ) (foldrᶜ-lemma eᶜ xs≈ys)

foldr-toCRoute-commute : ∀ {e f} (eᶜ : 𝑪 e) → toCRoute eᶜ ≈ᶜ f →
                      ∀ {xs ys} (foldrᶜ : 𝑪 (foldr _⊕_ e xs)) →
                      Pointwise (λ x y → x ≈ proj₁ y) xs ys →
                      toCRoute foldrᶜ ≈ᶜ foldr _⊕ᶜ_ f ys
foldr-toCRoute-commute eᶜ e≈f foldrᶜ []            = e≈f
foldr-toCRoute-commute eᶜ e≈f foldrᶜ (x≈y ∷ xs≈ys) =
  ⊕-cong x≈y (foldr-toCRoute-commute eᶜ e≈f (foldrᶜ-lemma eᶜ xs≈ys) xs≈ys)

σ-toCMatrix-commute : ∀ {X} (Xᶜ : 𝑪ₘ X) (σXᶜ : 𝑪ₘ (σ X)) →
                      toCMatrix σXᶜ ≈ᶜₘ σᶜ (toCMatrix Xᶜ)
σ-toCMatrix-commute {X} Xᶜ σXᶜ i j =
  foldr-toCRoute-commute (Iᶜ i j) (I≈toCI i j) (σXᶜ i j)
    (Pointwise.tabulate⁺ {g = λ k → A i k ▷ X k j , ▷-pres-𝑪 i k (Xᶜ k j)} (λ k → ≈-refl))
