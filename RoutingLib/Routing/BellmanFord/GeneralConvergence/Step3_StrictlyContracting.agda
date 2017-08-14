open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Nat using (ℕ; zero; suc; z≤n; s≤s; _∸_) renaming (_<_ to _<ℕ_; _≤_ to _≤ℕ_; _≟_ to _≟ℕ_)
open import Data.Nat.Properties using (n≤1+n)
open import Data.Fin.Properties using () renaming (_≟_ to _≟𝔽_)
open import Data.Product using (∃₂; _,_; _×_; proj₁)
open import Function using (_∘_)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary using (module DecTotalOrder)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; subst; subst₂; cong; cong₂; inspect; [_]) renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans)

open import RoutingLib.Routing.Definitions using (RoutingProblem; RoutingAlgebra)
open import RoutingLib.Data.Nat.Properties using (m<n≤o⇒o∸n<o∸m; n≢0⇒0<n; <⇒≤) renaming (≤-antisym to ≤ℕ-antisym; ≤-trans to ≤ℕ-trans)

open import RoutingLib.Routing.BellmanFord.GeneralConvergence.SufficientConditions

module RoutingLib.Routing.BellmanFord.GeneralConvergence.Step3_StrictlyContracting
  {a b ℓ n-1}
  {𝓡𝓐 : RoutingAlgebra a b ℓ}
  (𝓡𝓟 : RoutingProblem 𝓡𝓐 (suc n-1)) 
  (sc : SufficientConditions 𝓡𝓐)
  where
  
  open import RoutingLib.Routing.BellmanFord.GeneralConvergence.Step1_HeightFunction 𝓡𝓟 sc
  open import RoutingLib.Routing.BellmanFord.GeneralConvergence.Step2_UltrametricAlt 𝓡𝓟 sc
  open import RoutingLib.Routing.BellmanFord.GeneralConvergence.SufficientConditions.Properties 𝓡𝓟 sc using (σXᵢᵢ≈σYᵢᵢ; σXᵢⱼ≤Aᵢₖ▷Xₖⱼ; σXᵢⱼ≈Aᵢₖ▷Xₖⱼ⊎Iᵢⱼ)

  open import RoutingLib.Routing.BellmanFord 𝓡𝓟
  open import RoutingLib.Routing.BellmanFord.Properties 𝓡𝓟 using (Iᵢⱼ≡0#)

  open RoutingProblem 𝓡𝓟
  open SufficientConditions sc
  

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
    (dₑᵢⱼ≡dₛᵤₚ∸hσXᵢⱼ : dₑ (σ X i j) (σ Y i j) ≡ dₛᵤₚ ∸ h (σ X i j)) 
    where 

    h[σXᵢⱼ]≤h[σYᵢⱼ] : h (σ X i j) ≤ℕ h (σ Y i j)
    h[σXᵢⱼ]≤h[σYᵢⱼ] = dₑ≡dₛᵤₚ∸hx⇒hx≤hy dₑᵢⱼ≡dₛᵤₚ∸hσXᵢⱼ
    
    abstract

      -- Result for when the minimal disagreement lies on the diagonal of the matrices
      diagonal-result : j ≡ i → d (σ X) (σ Y) <ℕ d X Y
      diagonal-result ≡-refl = contradiction (σXᵢᵢ≈σYᵢᵢ X Y i) σXᵢⱼ≉σYᵢⱼ


      -- Result for when the minimal disagreement is taken from the identity matrix
      drop-result : j ≢ i → σ X i j ≈ 0# → d (σ X) (σ Y) <ℕ d X Y
      drop-result j≢i σXᵢⱼ≈0# = 
        contradiction 
          (≈-resp-h 
            (≤ℕ-antisym 
              h[σXᵢⱼ]≤h[σYᵢⱼ] 
              (subst (h (σ Y i j) ≤ℕ_) (h-resp-≈ (sym σXᵢⱼ≈0#)) (h-resp-≤ (0#-idₗ-⊕ (σ Y i j))))))
          σXᵢⱼ≉σYᵢⱼ


      -- Result for when the minimal disagreement is an extension of some path in the previous state
      extend-lemma : ∀ {k} → σ X i j ≈ A i k ▷ X k j → X k j ≉ Y k j
      extend-lemma {k} σXᵢⱼ≈Aᵢₖ▷Xₖⱼ Xₖⱼ≈Yₖⱼ = 
        σXᵢⱼ≉σYᵢⱼ (
          ≤-antisym 
            (≤-resp-h h[σXᵢⱼ]≤h[σYᵢⱼ]) 
            (≤-respᵣ-≈ (sym (trans σXᵢⱼ≈Aᵢₖ▷Xₖⱼ (▷-cong (A i k) Xₖⱼ≈Yₖⱼ))) (σXᵢⱼ≤Aᵢₖ▷Xₖⱼ Y i j k)))

      extend-result : ∀ {k} → j ≢ i → σ X i j ≈ A i k ▷ X k j → X k j ≉ 0# → d (σ X) (σ Y) <ℕ d X Y
      extend-result {k} j≢i σXᵢⱼ≈Aᵢₖ▷Xₖⱼ Xₖⱼ≉0# =
        begin
          suc (d (σ X) (σ Y))             ≡⟨ cong suc (≡-trans d≡dₑᵢⱼ dₑᵢⱼ≡dₛᵤₚ∸hσXᵢⱼ) ⟩ 
          suc (dₛᵤₚ ∸ h (σ X i j))        ≡⟨ cong suc (cong (dₛᵤₚ ∸_) (h-resp-≈ σXᵢⱼ≈Aᵢₖ▷Xₖⱼ)) ⟩ 
          suc (dₛᵤₚ ∸ h (A i k ▷ X k j))  ≤⟨ m<n≤o⇒o∸n<o∸m (h-resp-< (⊕-almost-strictly-absorbs-▷ (A i k) Xₖⱼ≉0#)) (<⇒≤ (s≤s h≤hₘₐₓ)) ⟩
          dₛᵤₚ ∸ h (X k j)                ≤⟨ dₛᵤₚ∸hXᵢⱼ≤d (extend-lemma σXᵢⱼ≈Aᵢₖ▷Xₖⱼ) ⟩
          d X Y
        ∎
        where open Data.Nat.≤-Reasoning


      -- Putting the three cases together to get the required result
      result : d (σ X) (σ Y) <ℕ d X Y
      result with j ≟𝔽 i 
      ...  | yes j≡i = diagonal-result j≡i
      ...  | no  j≢i with σXᵢⱼ≈Aᵢₖ▷Xₖⱼ⊎Iᵢⱼ X i j
      ...    | inj₂ σXᵢⱼ≈Iᵢⱼ = drop-result j≢i (trans σXᵢⱼ≈Iᵢⱼ (reflexive (Iᵢⱼ≡0# j≢i)))
      ...    | inj₁ (k , σXᵢⱼ≈Aᵢₖ▷Xₖⱼ) with X k j ≟ 0#
      ...      | yes Xₖⱼ≈0# = drop-result j≢i (trans σXᵢⱼ≈Aᵢₖ▷Xₖⱼ (trans (▷-cong (A i k) Xₖⱼ≈0#) (0#-anᵣ-▷ (A i k))))
      ...      | no  Xₖⱼ≉0# = extend-result j≢i σXᵢⱼ≈Aᵢₖ▷Xₖⱼ Xₖⱼ≉0#


  abstract

    open PostDisagreementResult using (result)
    open import RoutingLib.Function.Distance ℝ𝕄ₛ using (_StrContrOver_; _StrContrOnOrbitsOver_)
    open import RoutingLib.Function.Distance.Properties using (strContr⇒strContrOnOrbits)

    σ-strictlyContracting : σ StrContrOver d
    σ-strictlyContracting {X} {Y} Y≉X with σ X ≟ₘ σ Y | d X Y ≟ℕ 0
    ... | yes σX≈σY | yes d≡0 = contradiction (d≡0⇒X≈Y d≡0) (Y≉X ∘ ≈ₘ-sym)
    ... | yes σX≈σY | no  d≢0 rewrite X≈Y⇒d≡0 σX≈σY = n≢0⇒0<n d≢0
    ... | no  σX≉σY | _       with d-findWorstDisagreement σX≉σY
    ...   | i , j , σXᵢⱼ≉σYᵢⱼ , d≡dₑᵢⱼ , inj₁ dₑᵢⱼ≡dₛᵤₚ∸hσXᵢⱼ = result σXᵢⱼ≉σYᵢⱼ d≡dₑᵢⱼ dₑᵢⱼ≡dₛᵤₚ∸hσXᵢⱼ 
    ...   | i , j , σXᵢⱼ≉σYᵢⱼ , d≡dₑᵢⱼ , inj₂ dₑᵢⱼ≡dₛᵤₚ∸hσYᵢⱼ = 
      subst₂ _<ℕ_ (d-sym (σ Y) (σ X)) (d-sym Y X) (
        result 
          (σXᵢⱼ≉σYᵢⱼ ∘ sym) 
          (≡-trans (≡-trans (d-sym (σ Y) (σ X)) d≡dₑᵢⱼ) (dₑ-sym (σ X i j) (σ Y i j))) 
          (≡-trans (dₑ-sym (σ Y i j) (σ X i j)) dₑᵢⱼ≡dₛᵤₚ∸hσYᵢⱼ))

    σ-strictlyContractingOnOrbits : σ StrContrOnOrbitsOver d
    σ-strictlyContractingOnOrbits = strContr⇒strContrOnOrbits ℝ𝕄ₛ σ-strictlyContracting
