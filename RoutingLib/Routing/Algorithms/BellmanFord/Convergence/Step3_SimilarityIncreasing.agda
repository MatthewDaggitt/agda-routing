open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Nat using (ℕ; zero; suc; z≤n; s≤s; _∸_) renaming (_<_ to _<ℕ_; _≤_ to _≤ℕ_; _≟_ to _≟ℕ_)
open import Data.Nat.Properties using (n≤1+n)
open import Data.Fin.Properties using () renaming (_≟_ to _≟[Fin]_)
open import Data.Product using (∃₂; _,_; _×_; proj₁)
open import Function using (_∘_)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary using (module DecTotalOrder)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; subst; subst₂; cong; cong₂; inspect; [_]) renaming (sym to ≡-sym; trans to ≡-trans)

open import RoutingLib.Routing.Definitions
open import RoutingLib.Data.Nat.Properties using (m<n≤o⇨o∸n<o∸m; n≢0⇒0<n) renaming (≤-antisym to ≤ℕ-antisym; ≤-trans to ≤ℕ-trans)
open import RoutingLib.Function.HeightFunction

open import RoutingLib.Routing.Algorithms.BellmanFord.Convergence.SufficientConditions

module RoutingLib.Routing.Algorithms.BellmanFord.Convergence.Step3_SimilarityIncreasing
  {a b ℓ n-1}
  (rp : RoutingProblem a b ℓ (suc n-1))
  (cc : ConvergenceConditions (RoutingProblem.ra rp))
  (bhf : BoundedHeightFunction (ConvergenceConditions.≤-poset cc)) 
  where
  
  open import RoutingLib.Routing.Algorithms.BellmanFord.Convergence.Step2_Ultrametric rp cc bhf using (d; H; h≤H; d-sym; dₑ; dₑ-sym; d-metric; Xᵢⱼ≉Yᵢⱼ⇨H∸hXᵢⱼ≤d; dₑ≡H∸hx⇨hx≤hy; d≡0⇨X≈Y; X≈Y⇨d≡0; d≡dₑ; x≈y⇨dₑ≡0; dₑxy=hx⊎hy)
  open import RoutingLib.Routing.Algorithms.BellmanFord.Convergence.SufficientConditions.Properties rp cc using (σXᵢᵢ≈σYᵢᵢ; σXᵢⱼ≤Aᵢₖ▷Xₖⱼ; σXᵢⱼ≈Aᵢₖ▷Xₖⱼ⊎Iᵢⱼ)

  open import RoutingLib.Routing.Algorithms.BellmanFord rp
  open import RoutingLib.Routing.Algorithms.BellmanFord.Properties rp as BFProps using (Iᵢⱼ≈0#)

  open RoutingProblem rp
  open ConvergenceConditions cc
  open BoundedHeightFunction bhf
  
  ---------------------------
  -- Similarity increasing --
  ---------------------------
  -- In this module we show that an application of σ always strictly
  -- decreases the difference between two different routing matrices.
  -- The inner module below allows us to abstract over whether the
  -- minimal disagreement between two RMatrices X and Y has the smaller
  -- component in X or in Y. (i.e. dₑ(σXᵢⱼ,σYᵢⱼ) = h(Xᵢⱼ) 
  -- or h(Yᵢⱼ))

  module PostDisagreementResult 
    {X Y i j}
    (σXᵢⱼ≉σYᵢⱼ : σ X i j ≉ σ Y i j)
    (d≡dₑᵢⱼ : d (σ X) (σ Y) ≡ dₑ (σ X i j) (σ Y i j))
    (dₑᵢⱼ≡H∸hσXᵢⱼ : dₑ (σ X i j) (σ Y i j) ≡ H ∸ h (σ X i j)) 
    where 

    -- Useful property
    d≡H∸hσXᵢⱼ : d (σ X) (σ Y) ≡ H ∸ h (σ X i j)
    d≡H∸hσXᵢⱼ = ≡-trans d≡dₑᵢⱼ dₑᵢⱼ≡H∸hσXᵢⱼ

    abstract

      -- Result for when the minimal disagreement lies on the diagonal of the matrices
      diagonal-result : j ≡ i → d (σ X) (σ Y) <ℕ d X Y
      diagonal-result j≡i = 
        contradiction 
          (σXᵢᵢ≈σYᵢᵢ X Y i) 
          (subst (λ v → σ X i v ≉ σ Y i v) j≡i σXᵢⱼ≉σYᵢⱼ)


      -- Result for when the minimal disagreement element is taken from the identity matrix
      drop-result : j ≢ i → σ X i j ≈ 0# → d (σ X) (σ Y) <ℕ d X Y
      drop-result j≢i σXᵢⱼ≈0# = 
        contradiction 
          (≈-resp-h 
            (≤ℕ-antisym 
              (dₑ≡H∸hx⇨hx≤hy dₑᵢⱼ≡H∸hσXᵢⱼ) 
              (subst (h (σ Y i j) ≤ℕ_) (h-resp-≈ (sym σXᵢⱼ≈0#)) (h-resp-≤ (0#-idₗ-⊕ (σ Y i j))))))
          σXᵢⱼ≉σYᵢⱼ


      -- Result for when the minimal disagreement is an extension of some path in the previous state
      extend-lemma : ∀ {k} → σ X i j ≈ A i k ▷ X k j → X k j ≉ Y k j
      extend-lemma {k} σXᵢⱼ≈Aᵢₖ▷Xₖⱼ Xₖⱼ≈Yₖⱼ = 
        σXᵢⱼ≉σYᵢⱼ (
          ≤-antisym 
            (≤-resp-h (dₑ≡H∸hx⇨hx≤hy dₑᵢⱼ≡H∸hσXᵢⱼ)) 
            (≤-respᵣ-≈ (sym (trans σXᵢⱼ≈Aᵢₖ▷Xₖⱼ (▷-pres-≈ (A i k) Xₖⱼ≈Yₖⱼ))) (σXᵢⱼ≤Aᵢₖ▷Xₖⱼ Y i j k)))

      extend-result : ∀ {k} → j ≢ i → σ X i j ≈ A i k ▷ X k j → X k j ≉ 0# → d (σ X) (σ Y) <ℕ d X Y
      extend-result {k} j≢i σXᵢⱼ≈Aᵢₖ▷Xₖⱼ Xₖⱼ≉0# =
        begin
          suc (d (σ X) (σ Y))
        ≡⟨ cong suc d≡H∸hσXᵢⱼ ⟩ 
          suc (H ∸ h (σ X i j))
        ≡⟨ cong suc (cong (H ∸_) (h-resp-≈ σXᵢⱼ≈Aᵢₖ▷Xₖⱼ)) ⟩ 
          suc (H ∸ h (A i k ▷ X k j))
        ≤⟨ m<n≤o⇨o∸n<o∸m (h-resp-< (⊕-almost-strictly-absorbs-▷ (A i k) Xₖⱼ≉0#)) h≤H ⟩
          H ∸ h (X k j)
        ≤⟨ Xᵢⱼ≉Yᵢⱼ⇨H∸hXᵢⱼ≤d (extend-lemma σXᵢⱼ≈Aᵢₖ▷Xₖⱼ) ⟩
          d X Y
        ∎
        where open Data.Nat.≤-Reasoning


      -- Putting the three cases together to get the required result
      result : d (σ X) (σ Y) <ℕ d X Y
      result with j ≟[Fin] i 
      ...  | yes j≡i = diagonal-result j≡i
      ...  | no  j≢i with σXᵢⱼ≈Aᵢₖ▷Xₖⱼ⊎Iᵢⱼ X i j
      ...    | inj₂ σXᵢⱼ≈Iᵢⱼ = drop-result j≢i (trans σXᵢⱼ≈Iᵢⱼ (Iᵢⱼ≈0# j≢i))
      ...    | inj₁ (k , σXᵢⱼ≈Aᵢₖ▷Xₖⱼ) with X k j ≟ 0#
      ...      | yes Xₖⱼ≈0# = drop-result j≢i (trans σXᵢⱼ≈Aᵢₖ▷Xₖⱼ (trans (▷-pres-≈ (A i k) Xₖⱼ≈0#) (0#-anᵣ-▷ (A i k))))
      ...      | no  Xₖⱼ≉0# = extend-result j≢i σXᵢⱼ≈Aᵢₖ▷Xₖⱼ Xₖⱼ≉0#


  abstract

    open PostDisagreementResult using (result)
    open import RoutingLib.Function.Metric.Contraction Sₘ using (StrictlyContracting; StrictlyContractingOnOrbits; sc⇨scob)

    findWorstDisagreement : ∀ {X Y} → X ≉ₘ Y 
                              → ∃₂ λ i j 
                                 → X i j ≉ Y i j
                                   × d X Y ≡ dₑ (X i j) (Y i j)
                                   × (dₑ (X i j) (Y i j) ≡ H ∸ h (X i j) ⊎ dₑ (X i j) (Y i j) ≡ H ∸ h (Y i j))
    findWorstDisagreement {X} {Y} X≉Y with d X Y ≟ℕ 0 | d≡dₑ X Y 
    ... | yes d≡0 | _ = contradiction (d≡0⇨X≈Y d≡0) X≉Y
    ... | no  d≢0 | i , j , d≡dₑXᵢⱼYᵢⱼ with λ Xᵢⱼ≈Yᵢⱼ → d≢0 (≡-trans d≡dₑXᵢⱼYᵢⱼ (x≈y⇨dₑ≡0 Xᵢⱼ≈Yᵢⱼ))
    ...   | Xᵢⱼ≉Yᵢⱼ  = i , j , Xᵢⱼ≉Yᵢⱼ , d≡dₑXᵢⱼYᵢⱼ , dₑxy=hx⊎hy Xᵢⱼ≉Yᵢⱼ

    σ-strictlyContracting : StrictlyContracting d σ
    σ-strictlyContracting {X} {Y} X≉Y with σ X ≟ₘ σ Y | d X Y ≟ℕ 0
    ... | yes σX≈σY | yes d≡0 = contradiction (d≡0⇨X≈Y d≡0) X≉Y
    ... | yes σX≈σY | no  d≢0 rewrite X≈Y⇨d≡0 σX≈σY = n≢0⇒0<n d≢0
    ... | no  σX≉σY | _       with findWorstDisagreement σX≉σY
    ...   | i , j , σXᵢⱼ≉σYᵢⱼ , d≡dₑᵢⱼ , inj₁ dₑᵢⱼ≡H∸hσXᵢⱼ = result σXᵢⱼ≉σYᵢⱼ d≡dₑᵢⱼ dₑᵢⱼ≡H∸hσXᵢⱼ 
    ...   | i , j , σXᵢⱼ≉σYᵢⱼ , d≡dₑᵢⱼ , inj₂ dₑᵢⱼ≡H∸hσYᵢⱼ = 
      subst₂ _<ℕ_ (d-sym (σ Y) (σ X)) (d-sym Y X) (
        result 
          (σXᵢⱼ≉σYᵢⱼ ∘ sym) 
          (≡-trans (≡-trans (d-sym (σ Y) (σ X)) d≡dₑᵢⱼ) (dₑ-sym (σ X i j) (σ Y i j))) 
          (≡-trans (dₑ-sym (σ Y i j) (σ X i j)) dₑᵢⱼ≡H∸hσYᵢⱼ))

    σ-strictlyContractingOnOrbits : StrictlyContractingOnOrbits d σ
    σ-strictlyContractingOnOrbits = sc⇨scob σ-strictlyContracting
