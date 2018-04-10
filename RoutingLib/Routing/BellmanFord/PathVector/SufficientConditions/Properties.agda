import Algebra.FunctionProperties as FunctionProperties
import Algebra.FunctionProperties.Consequences as Consequences
open import Algebra.Structures
open import Data.Fin.Properties using () renaming (_≟_ to _≟𝔽_)
open import Data.Nat using (ℕ; suc; _<_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (∃; _×_; _,_; proj₁)
open import Function using (_∘_)
open import Relation.Binary using (DecTotalOrder; StrictTotalOrder)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; inspect; [_]; refl; sym)
import Relation.Binary.EqReasoning as EqReasoning
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Negation using (contradiction)

open import RoutingLib.Data.SimplePath
  using (SimplePath; valid; invalid; []; _∷_∣_∣_; length; _⇿_; _∈_; _∉_; notThere)
open import RoutingLib.Data.SimplePath.Properties
  using (length-cong; length<n; ∉-resp-≈ₚ)
open import RoutingLib.Data.SimplePath.Relation.Equality
open import RoutingLib.Data.SimplePath.NonEmpty.Properties
  using (_⇿?_; _∉?_)
import RoutingLib.Relation.Binary.NaturalOrder.Right as RNO
import RoutingLib.Relation.Binary.NonStrictToStrict.DecTotalOrder as NonStrictToStrict

open import RoutingLib.Routing.Definitions
open import RoutingLib.Routing.BellmanFord.PathVector.SufficientConditions
import RoutingLib.Routing.BellmanFord as BellmanFord

module RoutingLib.Routing.BellmanFord.PathVector.SufficientConditions.Properties
  {a b ℓ} {𝓡𝓐 : RoutingAlgebra a b ℓ}
  {n-1} {𝓡𝓟 : RoutingProblem 𝓡𝓐 n-1}
  (𝓟𝓢𝓒 : PathSufficientConditions 𝓡𝓟)
  where

  open RoutingProblem 𝓡𝓟
  open PathSufficientConditions 𝓟𝓢𝓒
  open FunctionProperties _≈_
    
  ------------------------------------------------------------------------------
  -- Additional properties of ⊕ and ▷
  
  ⊕-idem : Idempotent _⊕_
  ⊕-idem = Consequences.sel⇒idem S ⊕-sel

  ⊕-identityˡ : LeftIdentity 0# _⊕_
  ⊕-identityˡ x = ≈-trans (⊕-comm 0# x) (⊕-identityʳ x)

  ⊕-isSemigroup : IsSemigroup _≈_ _⊕_
  ⊕-isSemigroup = record
    { isEquivalence = ≈-isEquivalence
    ; assoc         = ⊕-assoc
    ; ∙-cong        = ⊕-cong
    }

  ⊕-absorbs-▷ : ∀ f x → x ≤₊ f ▷ x
  ⊕-absorbs-▷ f x with x ≟ 0#
  ... | no  x≉0 = proj₁ (⊕-strictlyAbsorbs-▷ f x≉0)
  ... | yes x≈0 = begin
    (f ▷ x)  ⊕ x  ≈⟨ ⊕-cong (▷-cong f x≈0) x≈0 ⟩
    (f ▷ 0#) ⊕ 0# ≈⟨ ⊕-cong (▷-zero f) ≈-refl ⟩
    0#       ⊕ 0# ≈⟨ ⊕-idem 0# ⟩
    0#            ≈⟨ ≈-sym x≈0 ⟩
    x             ∎
    where open EqReasoning S

  ------------------------------------------------------------------------------
  -- The induced right natural ordering over routes

  ≤₊-decTotalOrder : DecTotalOrder b ℓ ℓ
  ≤₊-decTotalOrder = RNO.≤-decTotalOrder _≈_ _⊕_ ⊕-isSemigroup _≟_ ⊕-comm ⊕-sel

  open DecTotalOrder ≤₊-decTotalOrder public
    using ()
    renaming
    ( _≤?_            to _≤₊?_
    ; refl            to ≤₊-refl
    ; reflexive       to ≤₊-reflexive
    ; trans           to ≤₊-trans
    ; antisym         to ≤₊-antisym
    ; poset           to ≤₊-poset
    ; total           to ≤₊-total
    ; ≤-resp-≈        to ≤₊-resp-≈
    ; totalOrder      to ≤₊-totalOrder
    ; isDecTotalOrder to ≤₊-isDecTotalOrder
    )

  open NonStrictToStrict ≤₊-decTotalOrder public
    using ()
    renaming
    ( _<?_     to _<₊?_
    ; <≤-trans to <≤₊-trans
    ; ≤<-trans to ≤<₊-trans
    ; <⇒≱      to <₊⇒≱₊
    ; ≤⇒≯      to ≤₊⇒≯₊
    ; ≰⇒>      to ≰₊⇒>₊
    ; <-asym   to <₊-asym
    ; <-strictPartialOrder to <₊-strictPartialOrder
    ; <-strictTotalOrder   to <₊-strictTotalOrder
    )
  
  ------------------------------------------------------------------------------
  -- Generic properties
  
  open BellmanFord 𝓡𝓟
  import RoutingLib.Routing.BellmanFord.Properties 𝓡𝓟 as P

  abstract
  
    σXᵢⱼ≈Aᵢₖ▷Xₖⱼ⊎Iᵢⱼ : ∀ X i j → (∃ λ k → σ X i j ≈ A i k ▷ X k j) ⊎ (σ X i j ≈ I i j)
    σXᵢⱼ≈Aᵢₖ▷Xₖⱼ⊎Iᵢⱼ = P.σXᵢⱼ≈Aᵢₖ▷Xₖⱼ⊎Iᵢⱼ ⊕-sel

    σXᵢᵢ≈Iᵢᵢ : ∀ X i → σ X i i ≈ I i i
    σXᵢᵢ≈Iᵢᵢ = P.σXᵢᵢ≈Iᵢᵢ ⊕-sel ⊕-assoc ⊕-comm ⊕-zeroʳ
    
    σXᵢᵢ≈σYᵢᵢ : ∀ X Y i → σ X i i ≈ σ Y i i
    σXᵢᵢ≈σYᵢᵢ = P.σXᵢᵢ≈σYᵢᵢ ⊕-sel ⊕-assoc ⊕-comm ⊕-zeroʳ

    σXᵢⱼ≤Aᵢₖ▷Xₖⱼ : ∀ X i j k → σ X i j ≤₊ A i k ▷ X k j
    σXᵢⱼ≤Aᵢₖ▷Xₖⱼ = P.σXᵢⱼ≤Aᵢₖ▷Xₖⱼ ⊕-idem ⊕-assoc ⊕-comm
    
    r≈0⇒e▷r≈0 : ∀ {e r} → r ≈ 0# → e ▷ r ≈ 0#
    r≈0⇒e▷r≈0 {e} {r} r≈0 = ≈-trans (▷-cong _ r≈0) (▷-zero e)

    e▷r≉0⇒r≉0 : ∀ {e r} → e ▷ r ≉ 0# → r ≉ 0#
    e▷r≉0⇒r≉0 e▷r≉0 r≈0 = e▷r≉0 (r≈0⇒e▷r≈0 r≈0)

  ------------------------------------------------------------------------------
  -- Path properties

  abstract
  
    p₀≈∅ : path 0# ≈ₚ invalid
    p₀≈∅ = r≈0⇒path[r]≈∅ ≈-refl

    p₁≈[] : path 1# ≈ₚ valid []
    p₁≈[] = r≈1⇒path[r]≈[] ≈-refl

    pᵣ≡∅⇒Aᵢⱼr≈0 : ∀ {i j r} → path r ≡ invalid → A i j ▷ r ≈ 0#
    pᵣ≡∅⇒Aᵢⱼr≈0 {i} {j} {r} pᵣ≡∅ = r≈0⇒e▷r≈0 (path[r]≈∅⇒r≈0 (≈ₚ-reflexive pᵣ≡∅))

    p[Iᵢᵢ]≈[] : ∀ i → path (I i i) ≈ₚ valid []
    p[Iᵢᵢ]≈[] i = r≈1⇒path[r]≈[] (≈-reflexive (P.Iᵢᵢ≡1# i))
    
    p[Iᵢⱼ]≈invalid : ∀ {i j} → j ≢ i → path (I i j) ≈ₚ invalid
    p[Iᵢⱼ]≈invalid j≢i = r≈0⇒path[r]≈∅ (≈-reflexive (P.Iᵢⱼ≡0# j≢i))
    
    p[σXᵢᵢ]≈[] : ∀ X i → path (σ X i i) ≈ₚ valid []
    p[σXᵢᵢ]≈[] X i = ≈ₚ-trans (path-cong (σXᵢᵢ≈Iᵢᵢ X i)) (p[Iᵢᵢ]≈[] i)

    p[Iᵢⱼ]≈[]⇒i≡j : ∀ {i j} → path (I i j) ≈ₚ valid [] → i ≡ j
    p[Iᵢⱼ]≈[]⇒i≡j {i} {j} p[Iᵢⱼ]≈[] with j ≟𝔽 i
    ... | yes refl = refl
    ... | no  _    = contradiction (≈ₚ-trans (≈ₚ-sym (r≈0⇒path[r]≈∅ ≈-refl)) p[Iᵢⱼ]≈[]) λ()
    
    p[σXᵢⱼ]≈[]⇒i≡j : ∀ X i j → path (σ X i j) ≈ₚ valid [] → i ≡ j
    p[σXᵢⱼ]≈[]⇒i≡j X i j p[σXᵢⱼ]≈[] with σXᵢⱼ≈Aᵢₖ▷Xₖⱼ⊎Iᵢⱼ X i j
    ... | inj₂ σXᵢⱼ≈Iᵢⱼ          = p[Iᵢⱼ]≈[]⇒i≡j (≈ₚ-trans (path-cong (≈-sym σXᵢⱼ≈Iᵢⱼ)) p[σXᵢⱼ]≈[])
    ... | inj₁ (k , σXᵢⱼ≈AᵢₖXₖⱼ) with A i k ▷ X k j ≟ 0#
    ...   | yes AᵢₖXₖⱼ≈0# = contradiction
      (≈ₚ-trans (≈ₚ-trans (≈ₚ-sym (r≈0⇒path[r]≈∅ AᵢₖXₖⱼ≈0#)) (path-cong (≈-sym σXᵢⱼ≈AᵢₖXₖⱼ))) p[σXᵢⱼ]≈[]) λ()
    ...   | no  AᵢₖXₖⱼ≉0# with path (X k j) | inspect path (X k j)
    ...       | invalid | [ p[Xₖⱼ]≡∅ ] = contradiction (pᵣ≡∅⇒Aᵢⱼr≈0 p[Xₖⱼ]≡∅) AᵢₖXₖⱼ≉0#
    ...       | valid q | [ p[Xₖⱼ]≡q ] with ≈ₚ-reflexive p[Xₖⱼ]≡q | (i , k) ⇿? q | i ∉? q
    ...         | pᵣ≈q | no ¬ik⇿q | _       = contradiction (path-reject pᵣ≈q (inj₁ ¬ik⇿q)) AᵢₖXₖⱼ≉0#
    ...         | pᵣ≈q | _        | no  i∈q = contradiction (path-reject pᵣ≈q (inj₂ i∈q))   AᵢₖXₖⱼ≉0#
    ...         | pᵣ≈q | yes ik⇿q | yes i∉q = contradiction (begin
      valid (_ ∷ q ∣ _ ∣ _) ≈⟨ ≈ₚ-sym (path-accept pᵣ≈q AᵢₖXₖⱼ≉0# ik⇿q i∉q) ⟩
      path (A i k ▷ X k j)  ≈⟨ path-cong (≈-sym σXᵢⱼ≈AᵢₖXₖⱼ) ⟩
      path (σ X i j)        ≈⟨ p[σXᵢⱼ]≈[] ⟩
      valid []              ∎) λ {(valid ())}
      where open EqReasoning (ℙₛ n)
    
    alignPathExtension : ∀ (X : RMatrix) i j k {u v p e⇿p i∉p} →
              path (A i k ▷ X k j) ≈ₚ valid ((u , v) ∷ p ∣ e⇿p ∣ i∉p) →
              i ≡ u × k ≡ v × path (X k j) ≈ₚ valid p
    alignPathExtension X i j k p[AᵢₖXₖⱼ]≈uv∷p with A i k ▷ X k j ≟ 0#
    ...     | yes AᵢₖXₖⱼ≈0# = contradiction (
      ≈ₚ-trans (≈ₚ-sym p[AᵢₖXₖⱼ]≈uv∷p) (
        ≈ₚ-trans (path-cong AᵢₖXₖⱼ≈0#) p₀≈∅)) λ()
    ...     | no  AᵢₖXₖⱼ≉0# with path (X k j) | inspect path (X k j)
    ...       | invalid | [ p[Xₖⱼ]≡∅ ] = contradiction (pᵣ≡∅⇒Aᵢⱼr≈0 p[Xₖⱼ]≡∅) AᵢₖXₖⱼ≉0#
    ...       | valid q | [ p[Xₖⱼ]≡q ] with ≈ₚ-reflexive p[Xₖⱼ]≡q | (i , k) ⇿? q | i ∉? q
    ...         | pᵣ≈q | no ¬ik⇿q | _       = contradiction (path-reject pᵣ≈q (inj₁ ¬ik⇿q)) AᵢₖXₖⱼ≉0#
    ...         | pᵣ≈q | _        | no  i∈q = contradiction (path-reject pᵣ≈q (inj₂ i∈q))   AᵢₖXₖⱼ≉0#
    ...         | pᵣ≈q | yes ik⇿q | yes i∉q with
      ≈ₚ-trans (≈ₚ-sym p[AᵢₖXₖⱼ]≈uv∷p)
        (path-accept pᵣ≈q AᵢₖXₖⱼ≉0# ik⇿q i∉q)
    ...           | valid (refl ∷ p≈q) = refl , refl , ≈ₚ-sym (valid p≈q)
    
    p[σXᵢⱼ]⇒σXᵢⱼ≈AᵢₖXₖⱼ : ∀ X i j {k l p e⇿p i∉p} →
                path (σ X i j) ≈ₚ valid ((l , k) ∷ p ∣ e⇿p ∣ i∉p) →
                i ≡ l × σ X i j ≈ A i k ▷ X k j × path (X k j) ≈ₚ valid p
    p[σXᵢⱼ]⇒σXᵢⱼ≈AᵢₖXₖⱼ X i j p[σXᵢⱼ]≈uv∷p with i ≟𝔽 j
    ... | yes refl = contradiction (≈ₚ-trans (≈ₚ-sym p[σXᵢⱼ]≈uv∷p) (p[σXᵢᵢ]≈[] X j)) λ{(valid ())}
    ... | no  i≢j with σXᵢⱼ≈Aᵢₖ▷Xₖⱼ⊎Iᵢⱼ X i j
    ...   | inj₂ σXᵢⱼ≈Iᵢⱼ           = contradiction (
      ≈ₚ-trans (≈ₚ-sym p[σXᵢⱼ]≈uv∷p) (
        ≈ₚ-trans (path-cong σXᵢⱼ≈Iᵢⱼ) (p[Iᵢⱼ]≈invalid (i≢j ∘ sym)))) λ()
    ...   | inj₁ (m , σXᵢⱼ≈AᵢₘXₘⱼ) with alignPathExtension X i j m
      (≈ₚ-trans (≈ₚ-sym (path-cong σXᵢⱼ≈AᵢₘXₘⱼ)) p[σXᵢⱼ]≈uv∷p)
    ...     | refl , refl , p[Xₖⱼ]≈p = refl , σXᵢⱼ≈AᵢₘXₘⱼ , p[Xₖⱼ]≈p
    
    k∉p[Iᵢⱼ] : ∀ i j k → k ∉ path (I i j)
    k∉p[Iᵢⱼ] i j k with j ≟𝔽 i
    ... | yes refl = ∉-resp-≈ₚ (≈ₚ-sym p₁≈[]) (valid notThere)
    ... | no  j≢i  = ∉-resp-≈ₚ (≈ₚ-sym p₀≈∅) invalid


  ------------------------------------------------------------------------------
  -- Size properties

  abstract
  
    size<n : ∀ r → size r < n
    size<n r = length<n (path _)

    size-cong : ∀ {r s} → r ≈ s → size r ≡ size s
    size-cong {r} {s} r≈s = length-cong (path-cong r≈s)
