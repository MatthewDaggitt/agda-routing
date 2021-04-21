--------------------------------------------------------------------------------
-- Agda routing library
--
-- This module contains some basic properties of F, the synchronous iteration
-- underlying vector based routing, under the assumption that the routing
-- algebra is a path-vector algebra.
--------------------------------------------------------------------------------

open import Data.Fin.Properties using (¬∀⟶∃¬; all?) renaming (_≟_ to _≟𝔽_)
open import Data.List using (List; foldr)
import Data.List.Relation.Unary.All.Properties as All
open import Data.List.Properties
open import Data.List.Relation.Binary.Pointwise as Pointwise
  using (Pointwise; []; _∷_)
open import Data.Nat using (_<_)
open import Data.Nat.Induction using (Acc; acc; <-wellFounded)
open import Data.Nat.Properties
  using (≤-reflexive; <-trans; module ≤-Reasoning)
open import Data.Product using (∃; ∃₂; _×_; _,_; proj₁)
open import Data.Sum using (inj₁; inj₂)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Unary using (Decidable)
import Relation.Binary.Reasoning.Setoid as SetoidReasoning

open import RoutingLib.Data.Matrix using (SquareMatrix)

open import RoutingLib.Routing.Algebra
open import RoutingLib.Routing.Basics.Network using (AdjacencyMatrix)
open import RoutingLib.Routing.Basics.Path.CertifiedI
open import RoutingLib.Routing.Basics.Path.CertifiedI.Properties
  using (∉ₚ-resp-≈ₚ; ≈ₚ-trans; ≈ₚ-sym; ≈ₚ-reflexive; ℙₛ; _∉ᵥₚ?_; _⇿ᵥ?_)
import RoutingLib.Routing.VectorBased.Synchronous as VectorBased

module RoutingLib.Routing.VectorBased.Synchronous.PathVector.Properties
  {a b ℓ n} {algebra : RawRoutingAlgebra a b ℓ}
  (isRoutingAlgebra : IsRoutingAlgebra algebra)
  (isPathAlgebra : IsCertifiedPathAlgebra algebra n)
  (A : AdjacencyMatrix algebra n)
  where

open RawRoutingAlgebra algebra
open IsCertifiedPathAlgebra isPathAlgebra

open import RoutingLib.Routing.Algebra.Properties.CertifiedPathAlgebra isRoutingAlgebra isPathAlgebra
open import RoutingLib.Routing.Algebra.Construct.Consistent isRoutingAlgebra isPathAlgebra A
open import RoutingLib.Routing.VectorBased.Synchronous.DistanceVector.Properties isRoutingAlgebra A

open VectorBased algebra A

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

  p[FXᵢᵢ]≈[] : ∀ X i → path (F X i i) ≈ₚ valid []
  p[FXᵢᵢ]≈[] X i = ≈ₚ-trans (path-cong (FXᵢᵢ≈Iᵢᵢ X i)) (p[Iᵢᵢ]≈[] i)

  p[FXᵢⱼ]≈[]⇒i≡j : ∀ X i j → path (F X i j) ≈ₚ valid [] → i ≡ j
  p[FXᵢⱼ]≈[]⇒i≡j X i j p[FXᵢⱼ]≈[] with FXᵢⱼ≈Aᵢₖ▷Xₖⱼ⊎Iᵢⱼ X i j
  ... | inj₂ FXᵢⱼ≈Iᵢⱼ          = p[Iᵢⱼ]≈[]⇒i≡j (≈ₚ-trans (path-cong (≈-sym FXᵢⱼ≈Iᵢⱼ)) p[FXᵢⱼ]≈[])
  ... | inj₁ (k , FXᵢⱼ≈AᵢₖXₖⱼ) with A i k ▷ X k j ≟ ∞#
  ...   | yes AᵢₖXₖⱼ≈∞ = contradiction
    (≈ₚ-trans (≈ₚ-trans (≈ₚ-sym (r≈∞⇒path[r]≈∅ AᵢₖXₖⱼ≈∞)) (path-cong (≈-sym FXᵢⱼ≈AᵢₖXₖⱼ))) p[FXᵢⱼ]≈[]) λ()
  ...   | no  AᵢₖXₖⱼ≉∞ with path (X k j) | inspect path (X k j)
  ...       | invalid | [ p[Xₖⱼ]≡∅ ] = contradiction (p[r]≡∅⇒f▷r≈∞ (A i k) p[Xₖⱼ]≡∅) AᵢₖXₖⱼ≉∞
  ...       | valid q | [ p[Xₖⱼ]≡q ] with ≈ₚ-reflexive p[Xₖⱼ]≡q | (i , k) ⇿ᵥ? q | i ∉ᵥₚ? q
  ...         | pᵣ≈q | no ¬ik⇿q | _       = contradiction (path-reject (A i k) pᵣ≈q (inj₁ ¬ik⇿q)) AᵢₖXₖⱼ≉∞
  ...         | pᵣ≈q | _        | no  i∈q = contradiction (path-reject (A i k) pᵣ≈q (inj₂ i∈q))   AᵢₖXₖⱼ≉∞
  ...         | pᵣ≈q | yes ik⇿q | yes i∉q = contradiction (begin
    valid (_ ∷ q ∣ _ ∣ _) ≈⟨ ≈ₚ-sym (path-accept (A i k) pᵣ≈q AᵢₖXₖⱼ≉∞ ik⇿q i∉q) ⟩
    path (A i k ▷ X k j)  ≈⟨ ≈ₚ-sym (path-cong FXᵢⱼ≈AᵢₖXₖⱼ) ⟩
    path (F X i j)        ≈⟨ p[FXᵢⱼ]≈[] ⟩
    valid []              ∎) λ {(valid ())}
    where open SetoidReasoning (ℙₛ n)

  alignPathExtension : ∀ (X : RoutingMatrix) i j k {u v p e⇿p i∉p} →
            path (A i k ▷ X k j) ≈ₚ valid ((u , v) ∷ p ∣ e⇿p ∣ i∉p) →
            i ≡ u × k ≡ v × path (X k j) ≈ₚ valid p
  alignPathExtension X i j k p[AᵢₖXₖⱼ]≈uv∷p with A i k ▷ X k j ≟ ∞#
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

  p[FXᵢⱼ]⇒FXᵢⱼ≈AᵢₖXₖⱼ : ∀ X i j {k l p e⇿p i∉p} →
              path (F X i j) ≈ₚ valid ((l , k) ∷ p ∣ e⇿p ∣ i∉p) →
              i ≡ l × F X i j ≈ A i k ▷ X k j × path (X k j) ≈ₚ valid p
  p[FXᵢⱼ]⇒FXᵢⱼ≈AᵢₖXₖⱼ X i j p[FXᵢⱼ]≈uv∷p with i ≟𝔽 j
  ... | yes refl = contradiction (≈ₚ-trans (≈ₚ-sym p[FXᵢⱼ]≈uv∷p) (p[FXᵢᵢ]≈[] X j)) λ{(valid ())}
  ... | no  i≢j with FXᵢⱼ≈Aᵢₖ▷Xₖⱼ⊎Iᵢⱼ X i j
  ...   | inj₂ FXᵢⱼ≈Iᵢⱼ           = contradiction (
    ≈ₚ-trans (≈ₚ-sym p[FXᵢⱼ]≈uv∷p) (
      ≈ₚ-trans (path-cong FXᵢⱼ≈Iᵢⱼ) (p[Iᵢⱼ]≈∅ (i≢j ∘ sym)))) λ()
  ...   | inj₁ (m , FXᵢⱼ≈AᵢₘXₘⱼ) with alignPathExtension X i j m
    (≈ₚ-trans (≈ₚ-sym (path-cong FXᵢⱼ≈AᵢₘXₘⱼ)) p[FXᵢⱼ]≈uv∷p)
  ...     | refl , refl , p[Xₖⱼ]≈p = refl , FXᵢⱼ≈AᵢₘXₘⱼ , p[Xₖⱼ]≈p

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

  F-pres-𝑪ₘ : ∀ {X} → 𝑪ₘ X → 𝑪ₘ (F X)
  F-pres-𝑪ₘ Xᶜ i j = foldr-preservesᵇ {P = 𝑪} ⊕-pres-𝑪
    (Iᶜ i j) (All.tabulate⁺ (λ k → ▷-pres-𝑪 i k (Xᶜ k j)))

  FXᵢⱼⁱ≈Aᵢₖ▷Xₖⱼ : ∀ X i j → 𝑰 (F X i j) → ∃ λ k → F X i j ≈ A i k ▷ X k j × 𝑰 (X k j)
  FXᵢⱼⁱ≈Aᵢₖ▷Xₖⱼ X i j FXᵢⱼⁱ with FXᵢⱼ≈Aᵢₖ▷Xₖⱼ⊎Iᵢⱼ X i j
  ... | inj₁ (k , FXᵢⱼ≈Aᵢₖ▷Xₖⱼ) = k , FXᵢⱼ≈Aᵢₖ▷Xₖⱼ , ▷-forces-𝑰 (𝑰-cong FXᵢⱼ≈Aᵢₖ▷Xₖⱼ FXᵢⱼⁱ)
  ... | inj₂ FXᵢⱼ≈Iᵢⱼ           = contradiction (𝑪-cong (≈-sym FXᵢⱼ≈Iᵢⱼ) (Iᶜ i j)) FXᵢⱼⁱ


  FXᵢⱼⁱ⇒Xₖⱼⁱ≉FXₖⱼ : ∀ X i j → 𝑰 (F X i j) →
                    ∃ λ k → X k j ≉ F X k j × 𝑰 (X k j) × size (X k j) < size (F X i j)
  FXᵢⱼⁱ⇒Xₖⱼⁱ≉FXₖⱼ X i j FXᵢⱼⁱ = reduction i FXᵢⱼⁱ (<-wellFounded (size (F X i j)))
    where
    reduction : ∀ l → 𝑰 (F X l j) → Acc _<_ (size (F X l j)) →
                ∃ λ k → X k j ≉ F X k j × 𝑰 (X k j) × size (X k j) < size (F X l j)
    reduction l FXₗⱼⁱ (acc rec) with FXᵢⱼⁱ≈Aᵢₖ▷Xₖⱼ X l j FXₗⱼⁱ
    ... | (k , FXₗⱼ≈AₗₖXₖⱼ , Xₖⱼⁱ) with ≤-reflexive (sizeⁱ-incr′ FXₗⱼⁱ FXₗⱼ≈AₗₖXₖⱼ)
    ...   | |Xₖⱼ|<|FXₗⱼ| with X k j ≟ F X k j
    ...     | no  Xₖⱼ≉FXₖⱼ = k , Xₖⱼ≉FXₖⱼ , Xₖⱼⁱ , |Xₖⱼ|<|FXₗⱼ|
    ...     | yes Xₖⱼ≈FXₖⱼ with subst (_< size (F X l j)) (size-cong Xₖⱼ≈FXₖⱼ) |Xₖⱼ|<|FXₗⱼ|
    ...       | |FXₖⱼ|<|FXₗⱼ| with reduction k (𝑰-cong Xₖⱼ≈FXₖⱼ Xₖⱼⁱ) (rec _ (|FXₖⱼ|<|FXₗⱼ|))
    ...         | (m , ≉ , i , lt) = m , ≉ , i , <-trans lt |FXₖⱼ|<|FXₗⱼ|

  fixedPointᶜ : ∀ {X} → F X ≈ₘ X → 𝑪ₘ X
  fixedPointᶜ {X} FX≈X with 𝑪ₘ? (F X)
  ... | yes FXᶜ = 𝑪ₘ-cong FX≈X FXᶜ
  ... | no  FXⁱ with 𝑰ₘ-witness FXⁱ
  ...   | i , j , FXᵢⱼⁱ with FXᵢⱼⁱ⇒Xₖⱼⁱ≉FXₖⱼ X _ _ FXᵢⱼⁱ
  ...     | k , Xₖⱼ≉FXₖⱼ , _ = contradiction (≈-sym (FX≈X k j)) Xₖⱼ≉FXₖⱼ


------------------------------------------------------------------------------
-- Consistent algebra properties

open VectorBased algebraᶜ Aᶜ using () renaming
  ( RoutingMatrix to CMatrix
  ; _≈ₘ_ to _≈ᶜₘ_
  ; I    to Ic
  ; F    to Fᶜ
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
                 Pointwise (λ x y → x ≈ projᵣ y) xs ys →
                 𝑪 (foldr _⊕_ e xs)
foldrᶜ-lemma eᶜ []            = eᶜ
foldrᶜ-lemma eᶜ (_∷_ {y = y , yᶜ} x≈y xs≈ys) =
  ⊕-pres-𝑪 (𝑪-cong (≈-sym x≈y) (recomputeᶜ yᶜ)) (foldrᶜ-lemma eᶜ xs≈ys)

foldr-toCRoute-commute : ∀ {e f} (eᶜ : 𝑪 e) → toCRoute eᶜ ≈ᶜ f →
                      ∀ {xs ys} (foldrᶜ : 𝑪 (foldr _⊕_ e xs)) →
                      Pointwise (λ x y → x ≈ projᵣ y) xs ys →
                      toCRoute foldrᶜ ≈ᶜ foldr _⊕ᶜ_ f ys
foldr-toCRoute-commute eᶜ e≈f foldrᶜ []            = e≈f
foldr-toCRoute-commute eᶜ e≈f foldrᶜ (x≈y ∷ xs≈ys) =
  ⊕-cong x≈y (foldr-toCRoute-commute eᶜ e≈f (foldrᶜ-lemma eᶜ xs≈ys) xs≈ys)

F-toCMatrix-commute : ∀ {X} (Xᶜ : 𝑪ₘ X) (FXᶜ : 𝑪ₘ (F X)) →
                      toCMatrix FXᶜ ≈ᶜₘ Fᶜ (toCMatrix Xᶜ)
F-toCMatrix-commute {X} Xᶜ FXᶜ i j =
  foldr-toCRoute-commute (Iᶜ i j) (I≈toCI i j) (FXᶜ i j)
    (Pointwise.tabulate⁺ {g = λ k → A i k ▷ X k j , ▷-pres-𝑪 i k (Xᶜ k j)} (λ k → ≈-refl))

F-toCMatrix-commute′ : ∀ {X} (Xᶜ : 𝑪ₘ X) → toCMatrix (F-pres-𝑪ₘ Xᶜ) ≈ᶜₘ Fᶜ (toCMatrix Xᶜ)
F-toCMatrix-commute′ Xᶜ = F-toCMatrix-commute Xᶜ (F-pres-𝑪ₘ Xᶜ)
