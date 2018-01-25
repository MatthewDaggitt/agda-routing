open import Algebra.FunctionProperties using (Op₂; Selective; Congruent₂)
open import Data.Nat using (ℕ; _<_; z≤n; s≤s; zero; suc)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Fin.Properties using () renaming (_≟_ to _≟𝔽_)
open import Data.Fin.Dec using (¬∀⟶∃¬; all?)
open import Data.List using (List; tabulate; _∷_; map; foldr)
open import Data.List.All.Properties using (tabulate⁺)
open import Data.List.Any using (here; there)
import Data.List.Any.Membership as Membership
open import Data.List.Any.Membership.Properties using (∈-map⁺)
open import Data.Product using (Σ; ∃; ∃₂; _,_; _×_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Level using (_⊔_)
open import Function using (_∘_; _on_)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; inspect; [_]; module ≡-Reasoning)
open import Relation.Binary.List.Pointwise using ([]; _∷_) renaming (Rel to ListRel)
open import Relation.Unary using () renaming (Decidable to DecidableU)
import Relation.Binary.On as On
import Relation.Binary.EqReasoning as EqReasoning

open import RoutingLib.Data.Graph.SimplePath2 using (SimplePath; valid; invalid; []; _∷ₐ_; _∷_∣_∣_; length; _⇿_; _∈_) renaming (_≈_ to _≈ₚ_)
open import RoutingLib.Data.Graph.SimplePath2.Properties using (ℙₛ; length-cong; length<n; ∷ₐ-accept; ∷ₐ-reject; ∷ₐ-cong; ∷ₐ-length) renaming (≈-sym to ≈ₚ-sym; ≈-trans to ≈ₚ-trans; ≈-reflexive to ≈ₚ-reflexive)
open import RoutingLib.Data.Graph.SimplePath2.NonEmpty.Properties using (_⇿?_; _∉?_)
open import RoutingLib.Data.Graph.SimplePath2.Enumeration
open import RoutingLib.Routing.Definitions
open import RoutingLib.Routing.BellmanFord.PathVector.SufficientConditions
open import RoutingLib.Routing.BellmanFord.DistanceVector.SufficientConditions
open import RoutingLib.Data.List.Properties using (foldr-×pres)
open import RoutingLib.Data.List.Uniqueness.Setoid using (Unique; []; _∷_)
open import RoutingLib.Data.List.Uniqueness.Setoid.Properties using (deduplicate!⁺)
import RoutingLib.Data.List.Relation.Pointwise as PW
import RoutingLib.Data.List.Membership.DecSetoid as RMembership
open import RoutingLib.Data.List.Membership.DecSetoid.Properties using (∈-deduplicate⁺; ∈-resp-≈)
open import RoutingLib.Data.Nat.Properties using (module ≤-Reasoning)
import RoutingLib.Routing.BellmanFord as BellmanFord
--open import RoutingLib.Routing.BellmanFord.Properties
open import RoutingLib.Algebra.FunctionProperties using (_Preservesₗ_)

module RoutingLib.Routing.BellmanFord.PathVector.Prelude
  {a b ℓ} {𝓡𝓐 : RoutingAlgebra a b ℓ}
  {n-1} {𝓡𝓟 : RoutingProblem 𝓡𝓐 (suc n-1)}
  (𝓟𝓢𝓒 : PathSufficientConditions 𝓡𝓟)
  where
  
  open RoutingProblem 𝓡𝓟 public
  open BellmanFord 𝓡𝓟 public
  open PathSufficientConditions 𝓟𝓢𝓒 public
  import RoutingLib.Routing.BellmanFord.Properties 𝓡𝓟 as P

  n : ℕ
  n = suc n-1

  abstract
  
    r≈0⇒e▷r≈0 : ∀ {e r} → r ≈ 0# → e ▷ r ≈ 0#
    r≈0⇒e▷r≈0 {e} {r} r≈0 = ≈-trans (▷-cong _ r≈0) (0#-an-▷ e)

    e▷r≉0⇒r≉0 : ∀ {e r} → e ▷ r ≉ 0# → r ≉ 0#
    e▷r≉0⇒r≉0 e▷r≉0 r≈0 = e▷r≉0 (r≈0⇒e▷r≈0 r≈0)

    σXᵢⱼ≈Aᵢₖ▷Xₖⱼ⊎Iᵢⱼ : ∀ X i j → (∃ λ k → σ X i j ≈ A i k ▷ X k j) ⊎ (σ X i j ≈ I i j)
    σXᵢⱼ≈Aᵢₖ▷Xₖⱼ⊎Iᵢⱼ = P.σXᵢⱼ≈Aᵢₖ▷Xₖⱼ⊎Iᵢⱼ ⊕-sel

{-
    p[r]≈∅⇒p[fr]≈∅ : ∀ f {r} → path r ≈ₚ invalid → path (f ▷ r) ≈ₚ invalid
    p[r]≈∅⇒p[fr]≈∅ f {r} pᵣ≈∅ = proj₁ r≈0⇔path[r]≈∅ (≈-trans (▷-cong f (proj₂ r≈0⇔path[r]≈∅ pᵣ≈∅)) (0#-an-▷ f))

-}
    p₀≈∅ : path 0# ≈ₚ invalid
    p₀≈∅ = r≈0⇒path[r]≈∅ ≈-refl

    p₁≈[] : path 1# ≈ₚ valid []
    p₁≈[] = r≈1⇒path[r]≈[] ≈-refl

  -----------------
  -- Consistency --
  -----------------
  
  𝑪 : Route → Set ℓ
  𝑪 r = weight (path r) ≈ r

  𝑪ₜ : RTable → Set _
  𝑪ₜ X = ∀ i → 𝑪 (X i)

  𝑪ₘ : RMatrix → Set _
  𝑪ₘ X = ∀ i j → 𝑪 (X i j)
  
  𝑰 : Route → Set _
  𝑰 r = ¬ 𝑪 r

  𝑰ₜ : RTable → Set _
  𝑰ₜ t = ¬ 𝑪ₜ t
  
  𝑰ₘ : RMatrix → Set _
  𝑰ₘ X = ¬ 𝑪ₘ X

  abstract
  
    -- Helper function for introducing an inconsistent route
  
    -- Decidability of consistency
  
    𝑪? : DecidableU 𝑪
    𝑪? r = weight (path r) ≟ r

    𝑪ₜ? : DecidableU 𝑪ₜ
    𝑪ₜ? t = all? (λ i → 𝑪? (t i))
  
    𝑪ₘ? : DecidableU 𝑪ₘ
    𝑪ₘ? X = all? (λ i → 𝑪ₜ? (X i))

    -- Congruency of consistency
    
    𝑪-cong : ∀ {r s} → r ≈ s → 𝑪 r → 𝑪 s
    𝑪-cong r≈s rᶜ = ≈-trans (≈-trans (weight-cong (path-cong (≈-sym r≈s))) rᶜ) r≈s
    
    𝑪ₜ-cong : ∀ {x y} → x ≈ₜ y → 𝑪ₜ x → 𝑪ₜ y
    𝑪ₜ-cong x≈y xᶜ i = 𝑪-cong (x≈y i) (xᶜ i)

    𝑪ₘ-cong : ∀ {X Y} → X ≈ₘ Y → 𝑪ₘ X → 𝑪ₘ Y
    𝑪ₘ-cong X≈Y Xᶜ i j = 𝑪-cong (X≈Y i j) (Xᶜ i j)

    𝑰-cong : ∀ {r s} → r ≈ s → 𝑰 r → 𝑰 s
    𝑰-cong r≈s rⁱ sᶜ = rⁱ (𝑪-cong (≈-sym r≈s) sᶜ)

    -- We can create a witness for 𝑰ₜ and 𝑰ₘ

    𝑰ₜ-witness : ∀ {x} → 𝑰ₜ x → ∃ λ i → 𝑰 (x i)
    𝑰ₜ-witness {x} xⁱ = ¬∀⟶∃¬ n _ (λ j → 𝑪? (x j)) xⁱ
    
    𝑰ₘ-witness : ∀ {X} → 𝑰ₘ X → ∃₂ λ i j → 𝑰 (X i j)
    𝑰ₘ-witness {X} Xⁱ with ¬∀⟶∃¬ n _ (λ i → all? (λ j → 𝑪? (X i j))) Xⁱ
    ... | (j , Xⱼⁱ) = j , 𝑰ₜ-witness Xⱼⁱ
    
    -- Consistent and inconsistent objects can never be equal

    𝑪𝑰⇒≉ : ∀ {r s} → 𝑪 r → 𝑰 s → r ≉ s
    𝑪𝑰⇒≉ rᶜ sⁱ r≈s = sⁱ (𝑪-cong r≈s rᶜ)

    𝑪𝑰⇒≉ₜ : ∀ {x y} → 𝑪ₜ x → 𝑰ₜ y → x ≉ₜ y
    𝑪𝑰⇒≉ₜ xᶜ yⁱ x≈y with 𝑰ₜ-witness yⁱ
    ... | j , yⱼⁱ = 𝑪𝑰⇒≉ (xᶜ j) yⱼⁱ (x≈y j)

    𝑪𝑰⇒≉ₘ : ∀ {X Y} → 𝑪ₘ X → 𝑰ₘ Y → X ≉ₘ Y
    𝑪𝑰⇒≉ₘ Xᶜ Yⁱ X≈Y with 𝑰ₘ-witness Yⁱ
    ... | i , j , Yᵢⱼⁱ = 𝑪𝑰⇒≉ (Xᶜ i j) Yᵢⱼⁱ (X≈Y i j)

    -- Consistency is preserved by ⊕ and ▷

    0ᶜ : 𝑪 0#
    0ᶜ = weight-cong p₀≈∅
  
    1ᶜ : 𝑪 1#
    1ᶜ = weight-cong p₁≈[]
  
    ⊕-pres-𝑪 : ∀ {r s} → 𝑪 r → 𝑪 s → 𝑪 (r ⊕ s)
    ⊕-pres-𝑪 {r} {s} rᶜ sᶜ with ⊕-sel r s
    ... | inj₁ r⊕s≈r = 𝑪-cong (≈-sym r⊕s≈r) rᶜ
    ... | inj₂ r⊕s≈s = 𝑪-cong (≈-sym r⊕s≈s) sᶜ

    rejectExtension : ∀ i j p r → ¬ ((i , j) ⇿ p) ⊎ i ∈ p → path r ≈ₚ p  → A i j ▷ r ≈ 0#
    rejectExtension i j p r neg p≈pᵣ = path[r]≈∅⇒r≈0 (begin
      path (A i j ▷ r)  ≈⟨ path-extension i j r ⟩
      (i , j) ∷ₐ path r ≈⟨ ∷ₐ-cong (i , j) p≈pᵣ ⟩
      (i , j) ∷ₐ p      ≈⟨ ∷ₐ-reject neg ⟩
      invalid           ∎)
      where open EqReasoning (ℙₛ {n})

    ∷ₐ-pres-𝑪 : ∀ i j {r} → 𝑪 r → weight ((i , j) ∷ₐ path r) ≈ A i j ▷ r
    ∷ₐ-pres-𝑪 i j {r} rᶜ with path r | inspect path r
    ... | invalid | _ = ≈-sym (≈-trans (▷-cong (A i j) (≈-sym rᶜ)) (0#-an-▷ (A i j)))
    ... | valid p | [ pᵣ≡vₚ ] with (i , j) ⇿? p | i ∉? p
    ...   | no ¬ij⇿p | _       = ≈-sym (rejectExtension i j (valid p) r (inj₁ λ {(valid ij⇿pᵣ) → ¬ij⇿p ij⇿pᵣ}) (≈ₚ-reflexive pᵣ≡vₚ))
    ...   | yes _    | no  i∈p = ≈-sym (rejectExtension i j (valid p) r (inj₂ λ {(valid i∉p) → i∈p i∉p}) (≈ₚ-reflexive pᵣ≡vₚ))
    ...   | yes _    | yes _   = ▷-cong (A i j) rᶜ
    
    ▷-pres-𝑪 : ∀ i j {r} → 𝑪 r → 𝑪 (A i j ▷ r)
    ▷-pres-𝑪 i j {r} rᶜ = ≈-trans (weight-cong (path-extension i j r)) (∷ₐ-pres-𝑪 i j rᶜ)

    ▷-forces-𝑰 : ∀ {i j r} → 𝑰 (A i j ▷ r) → 𝑰 r
    ▷-forces-𝑰 Aᵢⱼrⁱ rᶜ = Aᵢⱼrⁱ (▷-pres-𝑪 _ _ rᶜ)

    --𝑰-valid : ∀ r → 𝑰 r → ∃ λ p → path r


  -----------
  -- Other --
  -----------

  size : Route → ℕ
  size r = length (path r)

  size<n : ∀ r → size r < n
  size<n r = length<n (path _)

  size-cong : ∀ {r s} → r ≈ s → size r ≡ size s
  size-cong {r} {s} r≈s = length-cong (path-cong r≈s)

  size-incr : ∀ {i j r} → 𝑰 (A i j ▷ r) → suc (size r) ≡ size (A i j ▷ r)
  size-incr {i} {j} {r} Aᵢⱼrⁱ with path (A i j ▷ r) | inspect path (A i j ▷ r)
  ...   | invalid | [ pₐᵣ≡∅ ] = contradiction (≈-sym (path[r]≈∅⇒r≈0 (≈ₚ-reflexive pₐᵣ≡∅))) Aᵢⱼrⁱ
  ...   | valid q | [ pₐᵣ≡q ] = begin
    suc (length (path r))      ≡⟨ sym (∷ₐ-length i j (path r) (≈ₚ-trans (≈ₚ-sym (path-extension i j r)) (≈ₚ-reflexive pₐᵣ≡q))) ⟩
    length ((i , j) ∷ₐ path r) ≡⟨ length-cong (≈ₚ-sym (path-extension i j r)) ⟩
    length (path (A i j ▷ r))  ≡⟨ length-cong (≈ₚ-reflexive pₐᵣ≡q) ⟩
    length (valid q)           ∎
    where open ≡-Reasoning

  weight-path : ∀ p → path (weight p) ≈ₚ p
  weight-path invalid                     = p₀≈∅
  weight-path (valid [])                  = p₁≈[]
  weight-path (valid ((i , j) ∷ p ∣ ij⇿p ∣ i∉p)) = begin
    path (A i j ▷ weight (valid p))    ≈⟨ path-extension i j (weight (valid p)) ⟩
    (i , j) ∷ₐ path (weight (valid p)) ≈⟨ ∷ₐ-cong (i , j) (weight-path (valid p)) ⟩
    (i , j) ∷ₐ valid p                 ≈⟨ ∷ₐ-accept ij⇿p i∉p ⟩
    valid ((i , j) ∷ p ∣ ij⇿p ∣ i∉p)  ∎
    where open EqReasoning (ℙₛ {n})
    
  weightᶜ : ∀ p → 𝑪 (weight p)
  weightᶜ p = weight-cong (weight-path p)
  
  ----------------------------------------------------------------------------
  -- All paths operations preserve consistency

  Iᶜ : 𝑪ₘ I
  Iᶜ i j with j ≟𝔽 i
  ... | yes _ = 1ᶜ
  ... | no  _ = 0ᶜ

  σ-pres-𝑪ₘ : ∀ {X} → 𝑪ₘ X → 𝑪ₘ (σ X)
  σ-pres-𝑪ₘ Xᶜ i j = foldr-×pres {P = 𝑪} ⊕-pres-𝑪
    (tabulate⁺ (λ k → ▷-pres-𝑪 i k (Xᶜ k j))) (Iᶜ i j)

  ------------------------------------------------------------------------------
  -- If an entry in the routing matrix is inconsistent then it must have an
  -- inconsistent parent route
  
  module _ X i j (σXᵢⱼⁱ : 𝑰 (σ X i j)) where
  
    𝒊-parent : Fin n
    𝒊-parent with σXᵢⱼ≈Aᵢₖ▷Xₖⱼ⊎Iᵢⱼ X i j
    ... | inj₁ (k , σXᵢⱼ≈Aᵢₖ▷Xₖⱼ) = k
    ... | inj₂ σXᵢⱼ≈Iᵢⱼ           = contradiction (𝑪-cong (≈-sym σXᵢⱼ≈Iᵢⱼ) (Iᶜ i j)) σXᵢⱼⁱ

    𝒊-parentⁱ : 𝑰 (X 𝒊-parent j)
    𝒊-parentⁱ Xₖⱼᶜ with σXᵢⱼ≈Aᵢₖ▷Xₖⱼ⊎Iᵢⱼ X i j
    ... | inj₁ (k , σXᵢⱼ≈Aᵢₖ▷Xₖⱼ) = σXᵢⱼⁱ (𝑪-cong (≈-sym σXᵢⱼ≈Aᵢₖ▷Xₖⱼ) (▷-pres-𝑪 i k Xₖⱼᶜ))
    ... | inj₂ σXᵢⱼ≈Iᵢⱼ           = contradiction (𝑪-cong (≈-sym σXᵢⱼ≈Iᵢⱼ) (Iᶜ i j)) σXᵢⱼⁱ

{-
    𝒊-parent-size : size (σ X i j) ≡ suc (size (X 𝒊-parent j))
    𝒊-parent-size with σXᵢⱼ≈Aᵢₖ▷Xₖⱼ⊎Iᵢⱼ X i j
    ... | inj₁ (k , σXᵢⱼ≈Aᵢₖ▷Xₖⱼ) = trans (size-cong σXᵢⱼ≈Aᵢₖ▷Xₖⱼ) (▷-size (λ Aᵢₖ▷Xₖⱼ≈0 → σXᵢⱼⁱ (𝑪-cong (≈-sym (≈-trans σXᵢⱼ≈Aᵢₖ▷Xₖⱼ Aᵢₖ▷Xₖⱼ≈0)) 0ᶜ))) 
    ... | inj₂ σXᵢⱼ≈Iᵢⱼ           = contradiction (𝑪-cong (≈-sym σXᵢⱼ≈Iᵢⱼ) (Iᶜ i j)) σXᵢⱼⁱ
-}

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

  ▷ᶜ-cong : _▷ᶜ_ Preservesₗ _≈ᶜ_
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
    ; 1≉0                = 1≉0
    }

  𝓡𝓟ᶜ : RoutingProblem 𝓡𝓐ᶜ n
  𝓡𝓟ᶜ = record { A = _,_ }

  open RoutingProblem 𝓡𝓟ᶜ using () renaming (RTable to CTable; RMatrix to CMatrix; _≈ₘ_ to _≈ᶜₘ_; _≈ₜ_ to _≈ᶜₜ_; ≈-trans to ≈ᶜ-trans)
  open BellmanFord 𝓡𝓟ᶜ using () renaming (I to Ic; σ to σᶜ)

  -- Conversion functions
  
  toCRoute : ∀ {r} → 𝑪 r → CRoute
  toCRoute {r} rᶜ = _ , rᶜ

  toCTable : ∀ {x} → 𝑪ₜ x → CTable
  toCTable {x} xᶜ i = x i , xᶜ i
  
  toCMatrix : ∀ {X} → 𝑪ₘ X → CMatrix 
  toCMatrix {X} Xᶜ i j = X i j , Xᶜ i j

  -- Conversion properties
  
  toCTable-cong : ∀ {x y} (xᶜ : 𝑪ₜ x) (yᶜ : 𝑪ₜ y) → x ≈ₜ y → toCTable xᶜ ≈ᶜₜ toCTable yᶜ
  toCTable-cong _ _ X≈Y i = X≈Y i
  
  toCMatrix-cong : ∀ {X Y} (Xᶜ : 𝑪ₘ X) (Yᶜ : 𝑪ₘ Y) → X ≈ₘ Y → toCMatrix Xᶜ ≈ᶜₘ toCMatrix Yᶜ
  toCMatrix-cong _ _ X≈Y i j = X≈Y i j
    
  I≈toCI : ∀ i j → toCRoute (Iᶜ i j) ≈ᶜ Ic i j
  I≈toCI i j with j ≟𝔽 i
  ... | yes _ = ≈-refl
  ... | no  _ = ≈-refl


  foldrᶜ-lemma : ∀ {e xs} {ys : List CRoute} → 𝑪 e →
                   ListRel (λ x y → x ≈ proj₁ y) xs ys →
                   𝑪 (foldr _⊕_ e xs)
  foldrᶜ-lemma eᶜ []            = eᶜ
  foldrᶜ-lemma eᶜ (_∷_ {y = y , yᶜ} x≈y xs≈ys) = ⊕-pres-𝑪 (𝑪-cong (≈-sym x≈y) yᶜ) (foldrᶜ-lemma eᶜ xs≈ys)

  foldr-toCRoute-commute : ∀ {e f} (eᶜ : 𝑪 e) → toCRoute eᶜ ≈ᶜ f → 
                        ∀ {xs ys} (foldrᶜ : 𝑪 (foldr _⊕_ e xs)) →
                        ListRel (λ x y → x ≈ proj₁ y) xs ys →
                        toCRoute foldrᶜ ≈ᶜ foldr _⊕ᶜ_ f ys
  foldr-toCRoute-commute eᶜ e≈f foldrᶜ []            = e≈f
  foldr-toCRoute-commute eᶜ e≈f foldrᶜ (x≈y ∷ xs≈ys) = ⊕-cong x≈y (foldr-toCRoute-commute eᶜ e≈f (foldrᶜ-lemma eᶜ xs≈ys) xs≈ys)

  σ-toCMatrix-commute : ∀ {X} (Xᶜ : 𝑪ₘ X) (σXᶜ : 𝑪ₘ (σ X)) → toCMatrix σXᶜ ≈ᶜₘ σᶜ (toCMatrix Xᶜ)
  σ-toCMatrix-commute {X} Xᶜ σXᶜ i j = foldr-toCRoute-commute (Iᶜ i j) (I≈toCI i j) (σXᶜ i j)
      (PW.tabulate⁺ {g = λ k → A i k ▷ X k j , ▷-pres-𝑪 i k (Xᶜ k j)} (λ k → ≈-refl))
    


  ⊕ᶜ-strictlyAbsorbs-▷ᶜ : ∀ (s : CStep) {r : CRoute} → r ≉ᶜ (0# , 0ᶜ) → ((s ▷ᶜ r) ⊕ᶜ r ≈ᶜ r) × (r ≉ᶜ (s ▷ᶜ r))
  ⊕ᶜ-strictlyAbsorbs-▷ᶜ (i , j) r≉0 = ⊕-strictlyAbsorbs-▷ (A i j) r≉0



  open Membership Sᶜ using () renaming (_∈_ to _∈ₗ_)
  open RMembership DSᶜ using (deduplicate)
  
  pathToCRoute : SimplePath n → CRoute
  pathToCRoute p = weight p , weightᶜ p

  abstract
  
    allCRoutes : List CRoute
    allCRoutes = map pathToCRoute (allPaths n)
 
    ∈-allCRoutes : ∀ r → r ∈ₗ allCRoutes
    ∈-allCRoutes (r , rᶜ) = ∈-resp-≈ Sᶜ {v = pathToCRoute (path r)} {w = r , rᶜ} (∈-map⁺ ℙₛ Sᶜ weight-cong (∈-allPaths (path r))) rᶜ

  𝓢𝓒 : SufficientConditions 𝓡𝓐ᶜ
  𝓢𝓒 = record
    { ⊕-assoc = λ _ _ _ → ⊕-assoc _ _ _
    ; ⊕-sel   = λ _ _   → ⊕-sel _ _
    ; ⊕-comm  = λ _ _   → ⊕-comm _ _
    ; ⊕-almost-strictly-absorbs-▷ = ⊕ᶜ-strictlyAbsorbs-▷ᶜ
    
    ; 0#-idᵣ-⊕ = λ _ → 0#-idᵣ-⊕ _
    ; 0#-an-▷  = λ _ → 0#-an-▷ _
    ; 1#-anᵣ-⊕ = λ _ → 1#-anᵣ-⊕ _
    
    ; allRoutes   = allCRoutes
    ; ∈-allRoutes = ∈-allCRoutes
    }
