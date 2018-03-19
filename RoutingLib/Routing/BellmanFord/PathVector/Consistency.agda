open import Algebra.FunctionProperties using (Op₂; Selective; Congruent₂; Congruent₁)
open import Data.Nat using (ℕ; _<_; z≤n; s≤s; zero; suc)
open import Data.Nat.Properties using (≤-reflexive)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Fin.Properties using () renaming (_≟_ to _≟𝔽_)
open import Data.Fin.Dec using (¬∀⟶∃¬; all?)
open import Data.List using (List; tabulate; _∷_; map; foldr)
open import Data.List.All.Properties using (tabulate⁺)
open import Data.List.Any using (here; there)
import Data.List.Relation.Pointwise as Pointwise
import Data.List.Any.Membership as Membership
open import Data.List.Any.Membership.Properties using (∈-map⁺)
open import Data.Product using (Σ; ∃; ∃₂; _,_; _×_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Level using (_⊔_)
open import Function using (_∘_; _on_)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; inspect; [_]; module ≡-Reasoning)
open import Relation.Binary.List.Pointwise
  using ([]; _∷_) renaming (Rel to ListRel)
open import Relation.Unary using () renaming (Decidable to DecidableU)
import Relation.Binary.On as On
import Relation.Binary.EqReasoning as EqReasoning
open import Induction.WellFounded using (Acc; acc)
open import Induction.Nat using () renaming (<-well-founded to <-wellFounded)

open import RoutingLib.Data.SimplePath
  using (SimplePath; valid; invalid; []; _∷_∣_∣_; length; _⇿_; _∈_; _∉_; notThere)
open import RoutingLib.Data.SimplePath.Relation.Equality
open import RoutingLib.Data.SimplePath.Properties
  using (length-cong; length<n; ∉-resp-≈ₚ)
open import RoutingLib.Data.SimplePath.NonEmpty.Properties
  using (_⇿?_; _∉?_)
open import RoutingLib.Data.SimplePath.Enumeration
open import RoutingLib.Data.List.Properties using (foldr-presᵇ)
open import RoutingLib.Data.List.Uniqueness.Setoid using (Unique; []; _∷_)
open import RoutingLib.Data.List.Uniqueness.Setoid.Properties using (deduplicate!⁺)
import RoutingLib.Data.List.Membership.DecSetoid as RMembership
open import RoutingLib.Data.List.Membership.DecSetoid.Properties using (∈-deduplicate⁺; ∈-resp-≈)
open import RoutingLib.Data.Nat.Properties using (module ≤-Reasoning)

open import RoutingLib.Routing.Definitions
import RoutingLib.Routing.BellmanFord as BellmanFord
open import RoutingLib.Routing.BellmanFord.PathVector.SufficientConditions
open import RoutingLib.Routing.BellmanFord.DistanceVector.SufficientConditions
import RoutingLib.Routing.BellmanFord.PathVector.SufficientConditions.Properties
  as SufficientConditionsProperties

module RoutingLib.Routing.BellmanFord.PathVector.Consistency
  {a b ℓ} {𝓡𝓐 : RoutingAlgebra a b ℓ}
  {n-1} {𝓡𝓟 : RoutingProblem 𝓡𝓐 n-1}
  (𝓟𝓢𝓒 : PathSufficientConditions 𝓡𝓟)
  where

  open BellmanFord 𝓡𝓟
  open RoutingProblem 𝓡𝓟
  open PathSufficientConditions 𝓟𝓢𝓒
  open SufficientConditionsProperties 𝓟𝓢𝓒

  -----------------
  -- Consistency --
  -----------------
  
  𝑪 : Route → Set ℓ
  𝑪 r = weight (path r) ≈ r

  𝑪ₘ : RMatrix → Set _
  𝑪ₘ X = ∀ i j → 𝑪 (X i j)
  
  𝑰 : Route → Set _
  𝑰 r = ¬ 𝑪 r

  𝑰ₘ : RMatrix → Set _
  𝑰ₘ X = ¬ 𝑪ₘ X

  abstract
  
    -- Decidability of consistency
  
    𝑪? : DecidableU 𝑪
    𝑪? r = weight (path r) ≟ r

    𝑪ₘ? : DecidableU 𝑪ₘ
    𝑪ₘ? X = all? (λ i → all? (λ j → 𝑪? (X i j)))

    -- Congruency of consistency
    
    𝑪-cong : ∀ {r s} → r ≈ s → 𝑪 r → 𝑪 s
    𝑪-cong r≈s rᶜ = ≈-trans (≈-trans (weight-cong (path-cong (≈-sym r≈s))) rᶜ) r≈s

    𝑪ₘ-cong : ∀ {X Y} → X ≈ₘ Y → 𝑪ₘ X → 𝑪ₘ Y
    𝑪ₘ-cong X≈Y Xᶜ i j = 𝑪-cong (X≈Y i j) (Xᶜ i j)

    𝑰-cong : ∀ {r s} → r ≈ s → 𝑰 r → 𝑰 s
    𝑰-cong r≈s rⁱ sᶜ = rⁱ (𝑪-cong (≈-sym r≈s) sᶜ)

    -- We can create a witness for 𝑰ₜ and 𝑰ₘ
    
    𝑰ₘ-witness : ∀ {X} → 𝑰ₘ X → ∃₂ λ i j → 𝑰 (X i j)
    𝑰ₘ-witness {X} Xⁱ with ¬∀⟶∃¬ n _ (λ i → all? (λ j → 𝑪? (X i j))) Xⁱ
    ... | (j , Xⱼⁱ) = j , (¬∀⟶∃¬ n _ (λ k → 𝑪? (X j k)) Xⱼⁱ)
    
    -- Consistent and inconsistent objects can never be equal

    𝑪𝑰⇒≉ : ∀ {r s} → 𝑪 r → 𝑰 s → r ≉ s
    𝑪𝑰⇒≉ rᶜ sⁱ r≈s = sⁱ (𝑪-cong r≈s rᶜ)

    𝑪𝑰⇒≉ₘ : ∀ {X Y} → 𝑪ₘ X → 𝑰ₘ Y → X ≉ₘ Y
    𝑪𝑰⇒≉ₘ Xᶜ Yⁱ X≈Y with 𝑰ₘ-witness Yⁱ
    ... | i , j , Yᵢⱼⁱ = 𝑪𝑰⇒≉ (Xᶜ i j) Yᵢⱼⁱ (X≈Y i j)

    -- Consistency is preserved by ⊕ and ▷

    0ᶜ : 𝑪 0#
    0ᶜ = weight-cong p₀≈∅
  
    1ᶜ : 𝑪 1#
    1ᶜ = weight-cong p₁≈[]

    Iᶜ : 𝑪ₘ I
    Iᶜ i j with j ≟𝔽 i
    ... | yes _ = 1ᶜ
    ... | no  _ = 0ᶜ
    
    ⊕-pres-𝑪 : ∀ {r s} → 𝑪 r → 𝑪 s → 𝑪 (r ⊕ s)
    ⊕-pres-𝑪 {r} {s} rᶜ sᶜ with ⊕-sel r s
    ... | inj₁ r⊕s≈r = 𝑪-cong (≈-sym r⊕s≈r) rᶜ
    ... | inj₂ r⊕s≈s = 𝑪-cong (≈-sym r⊕s≈s) sᶜ

    ▷-pres-𝑪 : ∀ i j {r} → 𝑪 r → 𝑪 (A i j ▷ r)
    ▷-pres-𝑪 i j {r} rᶜ with A i j ▷ r ≟ 0#
    ... | yes Aᵢⱼ▷r≈0# = 𝑪-cong (≈-sym Aᵢⱼ▷r≈0#) 0ᶜ
    ... | no  Aᵢⱼ▷r≉0# with path r | inspect path r
    ...   | invalid | [ pᵣ≡∅ ] = contradiction (pᵣ≡∅⇒Aᵢⱼr≈0 pᵣ≡∅) Aᵢⱼ▷r≉0#
    ...   | valid q | [ pᵣ≡q ] with ≈ₚ-reflexive pᵣ≡q | (i , j) ⇿? q | i ∉? q
    ...     | pᵣ≈q | no ¬ij⇿q | _       = 𝑪-cong (≈-sym (path-reject pᵣ≈q (inj₁ ¬ij⇿q))) 0ᶜ
    ...     | pᵣ≈q | _        | no  i∈q = 𝑪-cong (≈-sym (path-reject pᵣ≈q (inj₂ i∈q))) 0ᶜ
    ...     | pᵣ≈q | yes ij⇿q | yes i∉q = begin
      weight (path (A i j ▷ r))                 ≈⟨ weight-cong (path-accept pᵣ≈q Aᵢⱼ▷r≉0# ij⇿q i∉q) ⟩
      weight (valid ((i , j) ∷ q ∣ ij⇿q ∣ i∉q)) ≡⟨⟩
      A i j ▷ weight (valid q)                  ≈⟨ ▷-cong (A i j) rᶜ ⟩
      A i j ▷ r                                 ∎
      where open EqReasoning S
      
    ▷-forces-𝑰 : ∀ {i j r} → 𝑰 (A i j ▷ r) → 𝑰 r
    ▷-forces-𝑰 Aᵢⱼrⁱ rᶜ = Aᵢⱼrⁱ (▷-pres-𝑪 _ _ rᶜ)

    σ-pres-𝑪ₘ : ∀ {X} → 𝑪ₘ X → 𝑪ₘ (σ X)
    σ-pres-𝑪ₘ Xᶜ i j = foldr-presᵇ {P = 𝑪} ⊕-pres-𝑪
      (Iᶜ i j) (tabulate⁺ (λ k → ▷-pres-𝑪 i k (Xᶜ k j)))
           
    ----------------------------------------------------------------------------
    -- A few more non-obvious properties relating to consistency

    size-incr : ∀ {i j r} → 𝑰 (A i j ▷ r) → suc (size r) ≡ size (A i j ▷ r)
    size-incr {i} {j} {r} Aᵢⱼ▷rⁱ with A i j ▷ r ≟ 0#
    ... | yes Aᵢⱼ▷r≈0# = contradiction (𝑪-cong (≈-sym Aᵢⱼ▷r≈0#) 0ᶜ) Aᵢⱼ▷rⁱ
    ... | no  Aᵢⱼ▷r≉0# with path r | inspect path r
    ...   | invalid | [ pᵣ≡∅ ] = contradiction (pᵣ≡∅⇒Aᵢⱼr≈0 pᵣ≡∅) Aᵢⱼ▷r≉0#
    ...   | valid q | [ pᵣ≡q ] with ≈ₚ-reflexive pᵣ≡q | (i , j) ⇿? q | i ∉? q
    ...     | pᵣ≈q | no ¬ij⇿q | _       = contradiction (path-reject pᵣ≈q (inj₁ ¬ij⇿q)) Aᵢⱼ▷r≉0#
    ...     | pᵣ≈q | _        | no  i∈q = contradiction (path-reject pᵣ≈q (inj₂ i∈q)) Aᵢⱼ▷r≉0#
    ...     | pᵣ≈q | yes ij⇿q | yes i∉q = sym (length-cong (path-accept pᵣ≈q Aᵢⱼ▷r≉0# ij⇿q i∉q))
    
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
        size (X k j)           <⟨ ≤-reflexive (size-incr (𝑰-cong σXₗⱼ≈AₗₖXₖⱼ σXₗⱼⁱ)) ⟩
        size (A l k ▷ X k j)   ≡⟨ size-cong (≈-sym σXₗⱼ≈AₗₖXₖⱼ) ⟩
        size (σ X l j)         ∎))

    weightᶜ : ∀ p → 𝑪 (weight p)
    weightᶜ invalid                            = 0ᶜ
    weightᶜ (valid [])                         = 1ᶜ
    weightᶜ (valid ((i , j) ∷ p ∣ e⇿p ∣ e∉p)) with A i j ▷ weight (valid p) ≟ 0#
    ... | yes Aᵢⱼ▷wₚ≈0 = 𝑪-cong (≈-sym Aᵢⱼ▷wₚ≈0) 0ᶜ
    ... | no  Aᵢⱼ▷wₚ≉0 with path (weight (valid p)) | inspect path (weight (valid p))
    ...   | invalid | [ p[wₚ]≡∅ ] = 𝑪-cong (≈-sym (pᵣ≡∅⇒Aᵢⱼr≈0 p[wₚ]≡∅)) 0ᶜ
    ...   | valid q | [ p[wₚ]≡q ] with ≈ₚ-reflexive p[wₚ]≡q | (i , j) ⇿? q | i ∉? q 
    ...     | p[wₚ]≈q | no ¬ij⇿q | _       = 𝑪-cong (≈-sym (path-reject p[wₚ]≈q (inj₁ ¬ij⇿q))) 0ᶜ
    ...     | p[wₚ]≈q | _        | no  i∈q = 𝑪-cong (≈-sym (path-reject p[wₚ]≈q (inj₂ i∈q))) 0ᶜ
    ...     | p[wₚ]≈q | yes ij⇿q | yes i∉q = begin
      weight (path (A i j ▷ weight (valid p)))    ≈⟨ weight-cong (path-accept p[wₚ]≈q Aᵢⱼ▷wₚ≉0 ij⇿q i∉q) ⟩
      weight (valid ((i , j) ∷ q ∣ ij⇿q ∣ i∉q))  ≡⟨⟩
      A i j ▷ weight (valid q)                    ≈⟨ ▷-cong (A i j) (weight-cong (≈ₚ-sym p[wₚ]≈q)) ⟩
      A i j ▷ weight (path (weight (valid p)))    ≈⟨ ▷-cong (A i j) (weightᶜ (valid p)) ⟩
      A i j ▷ weight (valid p)                    ∎
      where open EqReasoning S

    fixedᶜ : ∀ {X} → σ X ≈ₘ X → 𝑪ₘ X
    fixedᶜ {X} σX≈X with 𝑪ₘ? (σ X)
    ... | yes σXᶜ = 𝑪ₘ-cong σX≈X σXᶜ
    ... | no  σXⁱ with 𝑰ₘ-witness σXⁱ
    ...   | i , j , σXᵢⱼⁱ with σXᵢⱼⁱ⇒Xₖⱼⁱ≉σXₖⱼ X _ _ σXᵢⱼⁱ
    ...     | k , Xₖⱼ≉σXₖⱼ , _ = contradiction (≈-sym (σX≈X k j)) Xₖⱼ≉σXₖⱼ
  
  ------------------------------------------------------------------------------
  -- Consistent algebra

  infix 7 _⊕ᶜ_
  infix 6 _▷ᶜ_
  infix 4 _≈ᶜ_
    
  CRoute : Set _
  CRoute = Σ Route 𝑪

  CStep : Set _
  CStep = Fin n × Fin n
  
  _≈ᶜ_ : Rel CRoute _
  _≈ᶜ_ = _≈_ on proj₁

  _≉ᶜ_ : Rel CRoute _
  r ≉ᶜ s = ¬ (r ≈ᶜ s)
  
  _⊕ᶜ_ : Op₂ CRoute
  (r , rᶜ) ⊕ᶜ (s , sᶜ) = r ⊕ s , ⊕-pres-𝑪 rᶜ sᶜ
  
  _▷ᶜ_ : CStep → CRoute → CRoute
  (i , j) ▷ᶜ (r , rᶜ) = A i j ▷ r , ▷-pres-𝑪 i j rᶜ

  _≟ᶜ_ : Decidable _≈ᶜ_
  _ ≟ᶜ _ = _ ≟ _
  
  ≈ᶜ-isDecEquivalence : IsDecEquivalence _≈ᶜ_
  ≈ᶜ-isDecEquivalence = On.isDecEquivalence proj₁ ≈-isDecEquivalence

  Sᶜ : Setoid _ _
  Sᶜ = On.setoid {B = CRoute} S proj₁

  DSᶜ : DecSetoid _ _
  DSᶜ = On.decSetoid {B = CRoute} DS proj₁
  
  ⊕ᶜ-cong : Congruent₂ _≈ᶜ_ _⊕ᶜ_
  ⊕ᶜ-cong = ⊕-cong

  ▷ᶜ-cong : ∀ e {r s} → r ≈ᶜ s → e ▷ᶜ r ≈ᶜ e ▷ᶜ s
  ▷ᶜ-cong (i , j) = ▷-cong (A i j)

  𝓡𝓐ᶜ : RoutingAlgebra _ _ ℓ
  𝓡𝓐ᶜ = record
    { Step  = CStep
    ; Route = CRoute
    ; _⊕_   = _⊕ᶜ_
    ; _▷_   = _▷ᶜ_
    ; 0#    = 0# , 0ᶜ
    ; 1#    = 1# , 1ᶜ
    
    ; _≈_                = _≈ᶜ_
    ; ≈-isDecEquivalence = ≈ᶜ-isDecEquivalence
    ; ⊕-cong             = λ {x} {y} {u} {v} → ⊕ᶜ-cong {x} {y} {u} {v}
    ; ▷-cong             = ▷ᶜ-cong
    }

  𝓡𝓟ᶜ : RoutingProblem 𝓡𝓐ᶜ n-1
  𝓡𝓟ᶜ = record { A = _,_ }

  open RoutingProblem 𝓡𝓟ᶜ using ()
    renaming
    ( RMatrix to CMatrix
    ; _≈ₘ_ to _≈ᶜₘ_
    ; ≈-trans to ≈ᶜ-trans
    )
  open BellmanFord 𝓡𝓟ᶜ using ()
    renaming
    ( I to Ic
    ; σ to σᶜ
    )

  -- Conversion functions
  
  toCRoute : ∀ {r} → 𝑪 r → CRoute
  toCRoute {r} rᶜ = _ , rᶜ
  
  toCMatrix : ∀ {X} → 𝑪ₘ X → CMatrix 
  toCMatrix {X} Xᶜ i j = X i j , Xᶜ i j

  -- Conversion properties
  
  toCMatrix-cong : ∀ {X Y} (Xᶜ : 𝑪ₘ X) (Yᶜ : 𝑪ₘ Y) → X ≈ₘ Y →
                   toCMatrix Xᶜ ≈ᶜₘ toCMatrix Yᶜ
  toCMatrix-cong _ _ X≈Y i j = X≈Y i j
    
  I≈toCI : ∀ i j → toCRoute (Iᶜ i j) ≈ᶜ Ic i j
  I≈toCI i j with j ≟𝔽 i
  ... | yes _ = ≈-refl
  ... | no  _ = ≈-refl

  foldrᶜ-lemma : ∀ {e xs} {ys : List CRoute} → 𝑪 e →
                   ListRel (λ x y → x ≈ proj₁ y) xs ys →
                   𝑪 (foldr _⊕_ e xs)
  foldrᶜ-lemma eᶜ []            = eᶜ
  foldrᶜ-lemma eᶜ (_∷_ {y = y , yᶜ} x≈y xs≈ys) =
    ⊕-pres-𝑪 (𝑪-cong (≈-sym x≈y) yᶜ) (foldrᶜ-lemma eᶜ xs≈ys)

  foldr-toCRoute-commute : ∀ {e f} (eᶜ : 𝑪 e) → toCRoute eᶜ ≈ᶜ f → 
                        ∀ {xs ys} (foldrᶜ : 𝑪 (foldr _⊕_ e xs)) →
                        ListRel (λ x y → x ≈ proj₁ y) xs ys →
                        toCRoute foldrᶜ ≈ᶜ foldr _⊕ᶜ_ f ys
  foldr-toCRoute-commute eᶜ e≈f foldrᶜ []            = e≈f
  foldr-toCRoute-commute eᶜ e≈f foldrᶜ (x≈y ∷ xs≈ys) =
    ⊕-cong x≈y (foldr-toCRoute-commute eᶜ e≈f (foldrᶜ-lemma eᶜ xs≈ys) xs≈ys)

  σ-toCMatrix-commute : ∀ {X} (Xᶜ : 𝑪ₘ X) (σXᶜ : 𝑪ₘ (σ X)) →
                        toCMatrix σXᶜ ≈ᶜₘ σᶜ (toCMatrix Xᶜ)
  σ-toCMatrix-commute {X} Xᶜ σXᶜ i j =
    foldr-toCRoute-commute (Iᶜ i j) (I≈toCI i j) (σXᶜ i j)
      (Pointwise.tabulate⁺ {g = λ k → A i k ▷ X k j , ▷-pres-𝑪 i k (Xᶜ k j)} (λ k → ≈-refl))
    
  ⊕ᶜ-strictlyAbsorbs-▷ᶜ : ∀ (s : CStep) {r : CRoute} → r ≉ᶜ (0# , 0ᶜ) →
                          ((s ▷ᶜ r) ⊕ᶜ r ≈ᶜ r) × (r ≉ᶜ (s ▷ᶜ r))
  ⊕ᶜ-strictlyAbsorbs-▷ᶜ (i , j) r≉0 = ⊕-strictlyAbsorbs-▷ (A i j) r≉0

  open Membership Sᶜ using () renaming (_∈_ to _∈ₗ_)
  open RMembership DSᶜ using (deduplicate)
  
  pathToCRoute : SimplePath n → CRoute
  pathToCRoute p = weight p , weightᶜ p

  abstract
  
    allCRoutes : List CRoute
    allCRoutes = map pathToCRoute (allPaths n)
 
    ∈-allCRoutes : ∀ r → r ∈ₗ allCRoutes
    ∈-allCRoutes (r , rᶜ) = ∈-resp-≈ Sᶜ {v = pathToCRoute (path r)} {w = r , rᶜ}
      (∈-map⁺ (ℙₛ n) Sᶜ weight-cong (∈-allPaths (path r))) rᶜ

  𝓢𝓒 : SufficientConditions 𝓡𝓐ᶜ
  𝓢𝓒 = record
    { ⊕-assoc = λ _ _ _ → ⊕-assoc _ _ _
    ; ⊕-sel   = λ _ _   → ⊕-sel _ _
    ; ⊕-comm  = λ _ _   → ⊕-comm _ _
    ; ⊕-almost-strictly-absorbs-▷ = ⊕ᶜ-strictlyAbsorbs-▷ᶜ
    
    ; ▷-zero      = λ _ → ▷-zero _
    ; ⊕-identityʳ = λ _ → ⊕-identityʳ _
    ; ⊕-zeroʳ     = λ _ → ⊕-zeroʳ _
    
    ; allRoutes   = allCRoutes
    ; ∈-allRoutes = ∈-allCRoutes
    }
