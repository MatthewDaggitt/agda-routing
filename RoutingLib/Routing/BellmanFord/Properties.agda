open import Data.Nat using (suc; zero; _+_; _≤_)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Fin.Properties using () renaming (_≟_ to _≟𝔽_)
open import Data.Fin.Subset using (⊤; _∈_)
open import Data.Fin.Dec using (_∈?_)
open import Data.List using (tabulate)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (∃; ∃₂; _,_; _×_; proj₁; proj₂)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_) renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans)
open import Algebra.FunctionProperties.Consequences using (sel⇒idem)

open import RoutingLib.Routing.Definitions using (RoutingAlgebra; RoutingProblem)
open import RoutingLib.Data.List.Properties using (foldr≤ₗe; foldr≤ᵣxs)
open import RoutingLib.Data.List.Any.Membership.Properties using (foldr-∈; ∈-tabulate⁻; ∈-tabulate⁺)
open import RoutingLib.Data.List.All.Properties using (foldr-All₂; All₂-tabulate)
import RoutingLib.Routing.BellmanFord as BellmanFord

module RoutingLib.Routing.BellmanFord.Properties
  {a b ℓ n} {𝓡𝓐 : RoutingAlgebra a b ℓ} (𝓡𝓟 : RoutingProblem 𝓡𝓐 n)
  where

  -----------
  -- Setup --
  -----------

  open RoutingProblem 𝓡𝓟
  open BellmanFord 𝓡𝓟

  open import RoutingLib.Algebra.Selectivity.NaturalOrders S _⊕_ ⊕-cong using (_≤ᵣ_)
  open import Algebra.FunctionProperties _≈_ using (RightIdentity; RightZero; Idempotent; Commutative; Associative; Selective; LeftZero)
  
  abstract

    ---------------------
    -- Identity matrix --
    ---------------------

    Iᵢᵢ≡1# : ∀ i → I i i ≡ 1#
    Iᵢᵢ≡1# i with i ≟𝔽 i
    ... | yes _   = ≡-refl
    ... | no  i≢i = contradiction ≡-refl i≢i

    Iᵢᵢ-idᵣ-⊕ : RightZero 1# _⊕_ → ∀ i → RightZero (I i i) _⊕_
    Iᵢᵢ-idᵣ-⊕ 1#-anᵣ-⊕ i x rewrite Iᵢᵢ≡1# i = 1#-anᵣ-⊕ x
    
    Iᵢⱼ≡0# : ∀ {i j} → j ≢ i → I i j ≡ 0#
    Iᵢⱼ≡0# {i} {j} i≢j with j ≟𝔽 i
    ... | yes i≡j = contradiction i≡j i≢j
    ... | no  _   = ≡-refl

    Iᵢⱼ≡Iₖₗ : ∀ {i j k l} → j ≢ i → l ≢ k → I i j ≡ I k l
    Iᵢⱼ≡Iₖₗ j≢i l≢k = ≡-trans (Iᵢⱼ≡0# j≢i) (≡-sym (Iᵢⱼ≡0# l≢k))

    ----------------------------
    -- Synchronous properties --
    ----------------------------

    -- σ either extends the route by going through some k or it chooses a trivial route from the identity matrix
    σXᵢⱼ≈Aᵢₖ▷Xₖⱼ⊎Iᵢⱼ : Selective _⊕_ → ∀ X i j → (∃ λ k → σ X i j ≈ A i k ▷ X k j) ⊎ (σ X i j ≈ I i j)
    σXᵢⱼ≈Aᵢₖ▷Xₖⱼ⊎Iᵢⱼ ⊕-sel X i j with foldr-∈ S ⊕-sel (I i j) (tabulate (λ k → A i k ▷ X k j))
    ... | inj₁ σXᵢⱼ≈Iᵢⱼ  = inj₂ σXᵢⱼ≈Iᵢⱼ
    ... | inj₂ σXᵢⱼ∈extₖ = inj₁ (∈-tabulate⁻ S σXᵢⱼ∈extₖ)

    -- Under the following assumptions about ⊕, A▷ₘ always chooses the "best" option with respect to ⊕
    σXᵢⱼ≤Aᵢₖ▷Xₖⱼ : Idempotent _⊕_ → Associative _⊕_ → Commutative _⊕_ → ∀ X i j k → σ X i j ≤ᵣ A i k ▷ X k j
    σXᵢⱼ≤Aᵢₖ▷Xₖⱼ ⊕-idem ⊕-assoc ⊕-comm X i j k = foldr≤ᵣxs S ⊕-cong ⊕-idem ⊕-assoc ⊕-comm (I i j) (∈-tabulate⁺ S (λ k → A i k ▷ X k j) k)

    -- After an iteration, the diagonal of the RMatrix is always the identity
    σXᵢᵢ≈Iᵢᵢ : Selective _⊕_ → Associative _⊕_ → Commutative _⊕_ →
             RightZero 1# _⊕_ → ∀ X i → σ X i i ≈ I i i
    σXᵢᵢ≈Iᵢᵢ ⊕-sel ⊕-assoc ⊕-comm 1#-anᵣ-⊕ X i with σXᵢⱼ≈Aᵢₖ▷Xₖⱼ⊎Iᵢⱼ ⊕-sel X i i
    ... | inj₂ σXᵢᵢ≈Iᵢᵢ           = σXᵢᵢ≈Iᵢᵢ
    ... | inj₁ (k , σXᵢᵢ≈AᵢₖXₖⱼ) =
      begin
        σ X i i         ≈⟨ sym (foldr≤ₗe S ⊕-cong (sel⇒idem S ⊕-sel) ⊕-assoc ⊕-comm (I i i) (tabulate (λ k → A i k ▷ X k i))) ⟩
        σ X i i ⊕ I i i ≈⟨ Iᵢᵢ-idᵣ-⊕ 1#-anᵣ-⊕ i (σ X i i) ⟩
        I i i
      ∎
      where open import Relation.Binary.EqReasoning S
      
    -- After an iteration, the diagonals of any two RMatrices are equal
    σXᵢᵢ≈σYᵢᵢ : Selective _⊕_ → Associative _⊕_ →
              Commutative _⊕_ → RightZero 1# _⊕_ →
              ∀ X Y i → σ X i i ≈ σ Y i i
    σXᵢᵢ≈σYᵢᵢ ⊕-sel ⊕-assoc ⊕-comm 1#-anᵣ-⊕ X Y i = trans (σXᵢᵢ≈Iᵢᵢ ⊕-sel ⊕-assoc ⊕-comm 1#-anᵣ-⊕ X i) (sym (σXᵢᵢ≈Iᵢᵢ ⊕-sel ⊕-assoc ⊕-comm 1#-anᵣ-⊕ Y i))

    {-
    -- A sufficient (but not necessary condition) for σXᵢⱼ ≈ σYᵢⱼ
    σXᵢⱼ≈σYᵢⱼ : Selective _≈_ _⊕_ → Associative _≈_ _⊕_ → Commutative _≈_ _⊕_ → ∀ X Y i j
              → (∀ k → (A i k ▷ X k j ≈ A i k ▷ Y k j) ⊎ ((∃ λ l → (A i l ▷ X l j) <ᵣ (A i k ▷ X k j)) × (∃ λ m → (A i m ▷ Y m j) <ᵣ (A i k ▷ Y k j)))) → σ X i j ≈ σ Y i j
    σXᵢⱼ≈σYᵢⱼ ⊕-sel ⊕-assoc ⊕-comm X Y i j eqCon = foldrₓₛ≈foldrᵥₛ ⊕-sel ⊕-comm ⊕-assoc (I i j) (extensions X i j) (extensions Y i j) adjust
      where
      adjust : ∀ k → (lookup k (extensions X i j) ≈ lookup k (extensions Y i j))
        ⊎ ∃ (λ l → (lookup l (extensions X i j)) <ᵣ (lookup k (extensions X i j)))
          × ∃ (λ m → (lookup m (extensions Y i j)) <ᵣ (lookup k (extensions Y i j)))
      adjust k rewrite lookup-extensions X i j k | lookup-extensions Y i j k with eqCon k
      ... | inj₁ AᵢₖXₖⱼ≈AᵢₖYₖⱼ                           = inj₁ AᵢₖXₖⱼ≈AᵢₖYₖⱼ
      ... | inj₂ ((l , AᵢₗXₗⱼ<AₖⱼXₖⱼ) , (m , AᵢₘYₘⱼ<AᵢₖYₖⱼ)) = inj₂ ((l , subst₂ _<ᵣ_ (≡-sym (lookup-extensions X i j l)) ≡-refl AᵢₗXₗⱼ<AₖⱼXₖⱼ) , (m , subst₂ _<ᵣ_ (≡-sym (lookup-extensions Y i j m)) ≡-refl AᵢₘYₘⱼ<AᵢₖYₖⱼ))
    -}
