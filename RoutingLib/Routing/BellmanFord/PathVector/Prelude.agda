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
open import Data.Product using (Σ; ∃₂; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Level using (_⊔_)
open import Function using (_∘_; _on_)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; inspect; [_])
open import Relation.Binary.List.Pointwise using ([]; _∷_) renaming (Rel to ListRel)
open import Relation.Unary using () renaming (Decidable to DecidableU)
import Relation.Binary.On as On

open import RoutingLib.Data.Graph.SimplePath using (SimplePath; []; [_]; _∺_; _∷_; _∺_∣_; _∷_∣_; source; length) renaming (_≈_ to _≈ₚ_)
open import RoutingLib.Data.Graph.SimplePath.Properties using (ℙₛ; length<n; p≈q⇒|p|≡|q|) renaming (≈-refl to ≈ₚ-refl; ≈-trans to ≈ₚ-trans; ≈-reflexive to ≈ₚ-reflexive)
open import RoutingLib.Data.Graph.SimplePath.NonEmpty.Properties using (i∉p⇒i≢p₀) renaming (≈-refl to ≈ₙₑₚ-refl)
open import RoutingLib.Data.Graph.SimplePath.Enumeration
open import RoutingLib.Routing.Definitions
open import RoutingLib.Routing.BellmanFord.PathVector.SufficientConditions
open import RoutingLib.Routing.BellmanFord.DistanceVector.SufficientConditions
open import RoutingLib.Data.List.Properties using (foldr-×pres)
open import RoutingLib.Data.List.Uniqueness using (Unique; []; _∷_)
open import RoutingLib.Data.List.Uniqueness.Properties using (deduplicate!⁺)
import RoutingLib.Data.List.Any.Membership as RMembership
open import RoutingLib.Data.List.Any.Membership.Properties using (∈-deduplicate⁺; ∈-resp-≈)
import RoutingLib.Routing.BellmanFord as BellmanFord
open import RoutingLib.Routing.BellmanFord.Properties
open import RoutingLib.Algebra.FunctionProperties using (_Preservesₗ_)

module RoutingLib.Routing.BellmanFord.PathVector.Prelude
  {a b ℓ} {𝓡𝓐 : RoutingAlgebra a b ℓ}
  {n-1} {𝓡𝓟 : RoutingProblem 𝓡𝓐 (suc n-1)}
  (𝓟𝓢𝓒 : PathSufficientConditions 𝓡𝓟)
  where
  
  open RoutingProblem 𝓡𝓟 public
  open BellmanFord 𝓡𝓟 public
  open PathSufficientConditions 𝓟𝓢𝓒 public

  n : ℕ
  n = suc n-1

  r≈0⇒e▷r≈0 : ∀ {e r} → r ≈ 0# → e ▷ r ≈ 0#
  r≈0⇒e▷r≈0 {e} {r} r≈0 = ≈-trans (▷-cong _ r≈0) (0#-an-▷ e)

  e▷r≉0⇒r≉0 : ∀ {e r} → e ▷ r ≉ 0# → r ≉ 0#
  e▷r≉0⇒r≉0 e▷r≉0 r≈0 = e▷r≉0 (r≈0⇒e▷r≈0 r≈0)

  -----------------
  -- Consistency --
  -----------------
  
  data 𝑪 : Route → Set (b ⊔ ℓ) where
    𝒄-null  : ∀ {r} → r ≈ 0# → 𝑪 r
    𝒄-route : ∀ {r} → (r≉0 : r ≉ 0#) → weight (path r≉0) ≈ r → 𝑪 r
  
  𝑰 : Route → Set _
  𝑰 r = ¬ 𝑪 r

  𝒊-route : ∀ {r} → (r≉0 : r ≉ 0#) → weight (path r≉0) ≉ r → 𝑰 r
  𝒊-route r≉0 wᵣ≉r (𝒄-null  r≈0)   = r≉0 r≈0
  𝒊-route r≉0 wᵣ≉r (𝒄-route _ wᵣ≈r) = wᵣ≉r (≈-trans (weight-cong (path-cong ≈-refl _ _)) wᵣ≈r)

  𝑪? : DecidableU 𝑪
  𝑪? r with r ≟ 0#
  ... | yes r≈0 = yes (𝒄-null r≈0) 
  ... | no  r≉0 with weight (path r≉0) ≟ r
  ...   | yes wᵣ≈r = yes (𝒄-route r≉0 wᵣ≈r)
  ...   | no  wᵣ≉r = no  (𝒊-route r≉0 wᵣ≉r)

  𝑪-cong : ∀ {r s} → r ≈ s → 𝑪 r → 𝑪 s
  𝑪-cong r≈s (𝒄-null  r≈0)      = 𝒄-null (≈-trans (≈-sym r≈s) r≈0)
  𝑪-cong r≈s (𝒄-route r≉0 wᵣ≈r) = 𝒄-route s≉0 (≈-trans (weight-cong (path-cong (≈-sym r≈s) s≉0 r≉0)) (≈-trans wᵣ≈r r≈s))
    where s≉0 = r≉0 ∘ ≈-trans r≈s

  ⊕-pres-𝑪 : ∀ {r s} → 𝑪 r → 𝑪 s → 𝑪 (r ⊕ s)
  ⊕-pres-𝑪 {r} {s} rᶜ sᶜ with ⊕-sel r s
  ... | inj₁ r⊕s≈r = 𝑪-cong (≈-sym r⊕s≈r) rᶜ
  ... | inj₂ r⊕s≈s = 𝑪-cong (≈-sym r⊕s≈s) sᶜ

  ▷-pres-𝑪 : ∀ e {r} → 𝑪 r → 𝑪 (e ▷ r)
  ▷-pres-𝑪 e {_} (𝒄-null  r≈0)   = 𝒄-null (r≈0⇒e▷r≈0 r≈0)
  ▷-pres-𝑪 e {r} (𝒄-route r≉0 wᵣ≈r) with e ▷ r ≟ 0#
  ... | yes e▷r≈0 = 𝒄-null e▷r≈0
  ... | no  e▷r≉0 = 𝒄-route e▷r≉0 (path-consistency e r≉0 e▷r≉0 wᵣ≈r)



  𝑪ₘ : RMatrix → Set _
  𝑪ₘ X = ∀ i j → 𝑪 (X i j)

  𝑰ₘ : RMatrix → Set _
  𝑰ₘ X = ¬ 𝑪ₘ X

  abstract
  
    𝑪ₘ? : DecidableU 𝑪ₘ
    𝑪ₘ? X = all? (λ i → all? (λ j → 𝑪? (X i j)))
  
    𝑪ₘ-cong : ∀ {X Y} → X ≈ₘ Y → 𝑪ₘ X → 𝑪ₘ Y
    𝑪ₘ-cong X≈Y Xᶜ i j = 𝑪-cong (X≈Y i j) (Xᶜ i j)
  
    𝑰ₘ-witness : ∀ {X} → 𝑰ₘ X → ∃₂ λ i j → 𝑰 (X i j)
    𝑰ₘ-witness {X} ¬Xᶜ with ¬∀⟶∃¬ n _ (λ i → all? (λ j → 𝑪? (X i j))) ¬Xᶜ
    ... | (i , ¬Xᵢᶜ) with ¬∀⟶∃¬ n _ (λ j → 𝑪? (X i j)) ¬Xᵢᶜ
    ...   | (j , ¬Xᵢⱼᶜ) = i , j , ¬Xᵢⱼᶜ

  xᶜ∧yⁱ⇒x≉y : ∀ {x y} → 𝑪 x → 𝑰 y → x ≉ y
  xᶜ∧yⁱ⇒x≉y xᶜ yⁱ x≈y = yⁱ (𝑪-cong x≈y xᶜ)

  Xᶜ∧Yⁱ⇒X≉Y : ∀ {X Y} → 𝑪ₘ X → 𝑰ₘ Y → X ≉ₘ Y
  Xᶜ∧Yⁱ⇒X≉Y Xᶜ Yⁱ X≈Y with 𝑰ₘ-witness Yⁱ
  ... | i , j , Yᵢⱼⁱ = xᶜ∧yⁱ⇒x≉y (Xᶜ i j) Yᵢⱼⁱ (X≈Y i j)
  
  -----------
  -- Other --
  -----------
  
  Aᵢⱼ▷r≉0⇒i≢j : ∀ i j r → A i j ▷ r ≉ 0# → i ≢ j
  Aᵢⱼ▷r≉0⇒i≢j i j r Aᵢⱼ▷r≉0 with r ≟ 0#
  ... | yes r≈0 = contradiction (r≈0⇒e▷r≈0 r≈0) Aᵢⱼ▷r≉0
  ... | no  r≉0 with path r≉0 | inspect path r≉0
  ...   | []    | [ p[r]≡[] ] = proj₁ (path-extension₁ r≉0 Aᵢⱼ▷r≉0 (≈ₚ-reflexive p[r]≡[]))
  ...   | [ p ] | [ p[r]≡[p] ] with path-extension₂ r≉0 Aᵢⱼ▷r≉0 (≈ₚ-reflexive p[r]≡[p])
  ...     | (j≡p₀ , i∉p , _) = λ i≡j → i∉p⇒i≢p₀ i∉p (trans i≡j j≡p₀)
  
  size : Route → ℕ
  size r with r ≟ 0#
  ... | yes _   = 0
  ... | no  r≉0 = length (path r≉0)

  size<n : ∀ r → size r < n
  size<n r with r ≟ 0#
  ... | yes _ = s≤s z≤n
  ... | no  _ = length<n (path _)

  size-cong : ∀ {r s} → r ≈ s → size r ≡ size s
  size-cong {r} {s} r≈s with r ≟ 0# | s ≟ 0#
  ... | no  _   | no  _   = p≈q⇒|p|≡|q| (path-cong r≈s _ _)
  ... | no  r≉0 | yes s≈0 = contradiction (≈-trans r≈s s≈0) r≉0
  ... | yes r≈0 | no  s≉0 = contradiction (≈-trans (≈-sym r≈s) r≈0) s≉0
  ... | yes r≈0 | yes s≈0 = refl
  
  ▷-size : ∀ {i j r} → A i j ▷ r ≉ 0# → size (A i j ▷ r) ≡ suc (size r)
  ▷-size {i} {j} {r} Aᵢⱼ▷r≉0 with r ≟ 0# | A i j ▷ r ≟ 0#
  ... | yes r≈0 | _           = contradiction (r≈0⇒e▷r≈0 r≈0) Aᵢⱼ▷r≉0
  ... | _       | yes Aᵢⱼ▷r≈0 = contradiction Aᵢⱼ▷r≈0 Aᵢⱼ▷r≉0
  ... | no  r≉0 | no  Aᵢⱼ▷r≉0' with path r≉0 | inspect path r≉0
  ...   | []    | [ p[r]≡[] ] = p≈q⇒|p|≡|q| (proj₂ (path-extension₁ r≉0 Aᵢⱼ▷r≉0' (≈ₚ-reflexive p[r]≡[])))
  ...   | [ p ] | [ p[r]≡[p] ] with path-extension₂ r≉0 Aᵢⱼ▷r≉0' (≈ₚ-reflexive p[r]≡[p])
  ...     | _ , _ , p[Aᵢⱼ▷r]≈i∷p = p≈q⇒|p|≡|q| p[Aᵢⱼ▷r]≈i∷p

  weight-path : ∀ {p} (wₚ≉0 : weight p ≉ 0#) → path wₚ≉0 ≈ₚ p
  weight-path {[]}              wₚ≉0 = ≈ₚ-trans (path-cong ≈-refl wₚ≉0 1≉0) path[1]≈[]
  weight-path {[ i ∺ j ∣ i≢j ]} wₚ≉0 with path-extension₁ 1≉0 wₚ≉0 path[1]≈[]
  ... | i≢j' , p[Aᵢⱼ▷w]≈i∺j = ≈ₚ-trans p[Aᵢⱼ▷w]≈i∺j [ refl ∺ refl ]
  weight-path {[ i ∷ p ∣ i∉p ]} wₚ≉0 with path-extension₂ (wₚ≉0 ∘ r≈0⇒e▷r≈0) wₚ≉0 {p = p} (weight-path _)
  ... | _ , _ , p[Aᵢⱼ▷w]≈i∷p = ≈ₚ-trans p[Aᵢⱼ▷w]≈i∷p [ refl ∷ ≈ₙₑₚ-refl ]

  weightᶜ : ∀ p → 𝑪 (weight p)
  weightᶜ p with weight p ≟ 0#
  ... | yes wₚ≈0 = 𝒄-null wₚ≈0
  ... | no  wₚ≉0 = 𝒄-route wₚ≉0 (weight-cong {q = p} (weight-path wₚ≉0))
  
  ----------------------------------------------------------------------------
  -- All paths operations preserve consistency

  w₁≈1 : weight (path 1≉0) ≈ 1#
  w₁≈1 = ≈-trans (weight-cong path[1]≈[]) ≈-refl

  0ᶜ : 𝑪 0#
  0ᶜ = 𝒄-null ≈-refl
  
  1ᶜ : 𝑪 1#
  1ᶜ = 𝒄-route 1≉0 w₁≈1
  
  Iᶜ : 𝑪ₘ I
  Iᶜ i j with j ≟𝔽 i
  ... | yes _ = 1ᶜ
  ... | no  _ = 0ᶜ

  σ-pres-𝑪ₘ : ∀ {X} → 𝑪ₘ X → 𝑪ₘ (σ X)
  σ-pres-𝑪ₘ Xᶜ i j = foldr-×pres {P = 𝑪} ⊕-pres-𝑪
    (tabulate⁺ (λ k → ▷-pres-𝑪 (A i k) (Xᶜ k j))) (Iᶜ i j)

  ------------------------------------------------------------------------------
  -- If an entry in the routing matrix is inconsistent then it must have an
  -- inconsistent parent route

  module _ X i j (σXᵢⱼⁱ : 𝑰 (σ X i j)) where
  
    𝒊-parent : Fin n
    𝒊-parent with σXᵢⱼ≈Aᵢₖ▷Xₖⱼ⊎Iᵢⱼ 𝓡𝓟 ⊕-sel X i j
    ... | inj₁ (k , σXᵢⱼ≈Aᵢₖ▷Xₖⱼ) = k
    ... | inj₂ σXᵢⱼ≈Iᵢⱼ           = contradiction (𝑪-cong (≈-sym σXᵢⱼ≈Iᵢⱼ) (Iᶜ i j)) σXᵢⱼⁱ

    𝒊-parentⁱ : 𝑰 (X 𝒊-parent j)
    𝒊-parentⁱ Xₖⱼᶜ with σXᵢⱼ≈Aᵢₖ▷Xₖⱼ⊎Iᵢⱼ 𝓡𝓟 ⊕-sel X i j
    ... | inj₁ (k , σXᵢⱼ≈Aᵢₖ▷Xₖⱼ) = contradiction (𝑪-cong (≈-sym σXᵢⱼ≈Aᵢₖ▷Xₖⱼ) (▷-pres-𝑪 (A i k) Xₖⱼᶜ)) σXᵢⱼⁱ
    ... | inj₂ σXᵢⱼ≈Iᵢⱼ           = contradiction (𝑪-cong (≈-sym σXᵢⱼ≈Iᵢⱼ) (Iᶜ i j)) σXᵢⱼⁱ

    𝒊-parent-size : size (σ X i j) ≡ suc (size (X 𝒊-parent j))
    𝒊-parent-size with σXᵢⱼ≈Aᵢₖ▷Xₖⱼ⊎Iᵢⱼ 𝓡𝓟 ⊕-sel X i j
    ... | inj₁ (k , σXᵢⱼ≈Aᵢₖ▷Xₖⱼ) = trans (size-cong σXᵢⱼ≈Aᵢₖ▷Xₖⱼ) (▷-size (λ Aᵢₖ▷Xₖⱼ≈0 → σXᵢⱼⁱ (𝑪-cong (≈-sym (≈-trans σXᵢⱼ≈Aᵢₖ▷Xₖⱼ Aᵢₖ▷Xₖⱼ≈0)) 0ᶜ))) 
    ... | inj₂ σXᵢⱼ≈Iᵢⱼ           = contradiction (𝑪-cong (≈-sym σXᵢⱼ≈Iᵢⱼ) (Iᶜ i j)) σXᵢⱼⁱ

  ------------------------------------------------------------------------------
  -- Consistent algebra

  infix 7 _⊕ᶜ_
  infix 6 _▷ᶜ_
  infix 4 _≈ᶜ_
    
  CRoute : Set _
  CRoute = Σ Route 𝑪

  _≈ᶜ_ : Rel CRoute _
  _≈ᶜ_ = _≈_ on proj₁
  
  _⊕ᶜ_ : Op₂ CRoute
  (r , rᶜ) ⊕ᶜ (s , sᶜ) = r ⊕ s , ⊕-pres-𝑪 rᶜ sᶜ
  
  _▷ᶜ_ : Step → CRoute → CRoute
  e ▷ᶜ (r , rᶜ) = e ▷ r , ▷-pres-𝑪 e rᶜ

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
  ▷ᶜ-cong e = ▷-cong e 

  𝓡𝓐ᶜ : RoutingAlgebra a (b ⊔ ℓ) ℓ
  𝓡𝓐ᶜ = record
    { Step  = Step
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
  𝓡𝓟ᶜ = record { A = A }

  open RoutingProblem 𝓡𝓟ᶜ using () renaming (RMatrix to CMatrix; _≈ₘ_ to _≈ᶜₘ_; ≈-trans to ≈ᶜ-trans)
  open BellmanFord 𝓡𝓟ᶜ using () renaming (I to Ic; σ to σᶜ)
  
  toCRoute : ∀ {r} → 𝑪 r → CRoute
  toCRoute {r} rᶜ = _ , rᶜ

  toCMatrix : ∀ {X} → 𝑪ₘ X → CMatrix 
  toCMatrix {X} Xᶜ i j = X i j , Xᶜ i j

  toIMatrix : CMatrix → RMatrix
  toIMatrix X i j = proj₁ (X i j)

  toCMatrix-cong : ∀ {X Y} (Xᶜ : 𝑪ₘ X) (Yᶜ : 𝑪ₘ Y) → X ≈ₘ Y → toCMatrix Xᶜ ≈ᶜₘ toCMatrix Yᶜ
  toCMatrix-cong _ _ X≈Y i j = X≈Y i j
  
  postulate I≈toCI : ∀ i j → toCRoute (Iᶜ i j) ≈ᶜ Ic i j
  {-
  I≈toCI i j with j ≟𝔽 i
  ... | yes _ = {!!}
  ... | no  _ = ?
  -}

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
  σ-toCMatrix-commute {X} Xᶜ σXᶜ i j =
    foldr-toCRoute-commute (Iᶜ i j) (I≈toCI i j) (σXᶜ i j)
      (pw-tabulate⁺ {f = λ k → A i k ▷ X k j} {g = λ k → A i k ▷ X k j , ▷-pres-𝑪 (A i k) (Xᶜ k j)} (λ k → ≈-refl))
    where
    pw-tabulate⁺ : ∀ {a b ℓ} {A : Set a} {B : Set b} {_~_ : REL A B ℓ} →
                     ∀ {n} {f : Fin n → A} {g : Fin n → B} → (∀ i → f i ~ g i) →
                     ListRel _~_ (tabulate f) (tabulate g)
    pw-tabulate⁺ {n = zero} f~g  = []
    pw-tabulate⁺ {n = suc n} f~g = (f~g fzero) ∷ pw-tabulate⁺ (f~g ∘ fsuc)


  open Membership Sᶜ using (_∈_)
  open RMembership Sᶜ using (deduplicate)
  
  pathToCRoute : SimplePath n → CRoute
  pathToCRoute p = weight p , weightᶜ p

  abstract
  
    allCRoutes : List CRoute
    allCRoutes = deduplicate _≟ᶜ_ ((0# , 0ᶜ) ∷ map pathToCRoute (allPaths n))
 
    allCRoutes! : Unique Sᶜ allCRoutes
    allCRoutes! = deduplicate!⁺ Sᶜ _≟ᶜ_ ((0# , 0ᶜ) ∷ map pathToCRoute (allPaths n)) 

    ∈-allCRoutes : ∀ r → r ∈ allCRoutes
    ∈-allCRoutes (r , 𝒄-null  r≈0)      = ∈-deduplicate⁺ Sᶜ _≟ᶜ_ {x = (r , 𝒄-null  r≈0)}     {xs = (0# , 0ᶜ) ∷ map pathToCRoute (allPaths n)} (here r≈0)
    ∈-allCRoutes (r , 𝒄-route r≉0 wᵣ≈r) = ∈-deduplicate⁺ Sᶜ _≟ᶜ_ {x = (r , 𝒄-route r≉0 wᵣ≈r)} {xs = (0# , 0ᶜ) ∷ map pathToCRoute (allPaths n)} (there test)
      where
      test : (r , 𝒄-route r≉0 wᵣ≈r) ∈ map pathToCRoute (allPaths n)
      test = ∈-resp-≈ Sᶜ  {v = pathToCRoute (path r≉0)} {w = r , 𝒄-route r≉0 wᵣ≈r} (∈-map⁺ ℙₛ Sᶜ weight-cong (∈-allPaths (path r≉0))) wᵣ≈r



  𝓢𝓒 : SufficientConditions 𝓡𝓐ᶜ
  𝓢𝓒 = record
    { ⊕-assoc = λ _ _ _ → ⊕-assoc _ _ _
    ; ⊕-sel   = λ _ _   → ⊕-sel _ _
    ; ⊕-comm  = λ _ _   → ⊕-comm _ _
    ; ⊕-almost-strictly-absorbs-▷ = λ e r → ⊕-almost-strictly-absorbs-▷ e r
    
    ; 0#-idᵣ-⊕ = λ _ → 0#-idᵣ-⊕ _
    ; 0#-an-▷  = λ _ → 0#-an-▷ _
    ; 1#-anᵣ-⊕ = λ _ → 1#-anᵣ-⊕ _
    
    ; routes-enumerable = record { X = allCRoutes , allCRoutes! ; isEnumeration = ∈-allCRoutes }
    }
