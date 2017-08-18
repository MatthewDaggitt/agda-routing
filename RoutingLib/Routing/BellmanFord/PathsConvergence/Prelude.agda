open import Algebra.FunctionProperties using (Selective)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Fin.Properties using () renaming (_≟_ to _≟𝔽_)
open import Data.List using (tabulate)
open import Data.List.All.Properties using (tabulate⁺)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import Function using (_∘_)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary using (REL)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Binary.List.Pointwise using ([]; _∷_) renaming (Rel to ListRel)

open import RoutingLib.Data.Graph using (Graph)
open import RoutingLib.Data.Graph.SimplePath using ([])
open import RoutingLib.Routing.Definitions
open import RoutingLib.Routing.BellmanFord.PathsConvergence.SufficientConditions
open import RoutingLib.Data.List.Properties using (foldr-×pres)
import RoutingLib.Routing.AlgebraicPaths.Consistent as ConsistentPaths
import RoutingLib.Routing.AlgebraicPaths.Inconsistent as InconsistentPaths
import RoutingLib.Routing.BellmanFord as BellmanFord
open import RoutingLib.Routing.BellmanFord.Properties
  
module RoutingLib.Routing.BellmanFord.PathsConvergence.Prelude
  {a b ℓ} (𝓡𝓐 : RoutingAlgebra a b ℓ)
  (⊕-sel : Selective (RoutingAlgebra._≈_ 𝓡𝓐) (RoutingAlgebra._⊕_ 𝓡𝓐))
  {n : ℕ}
  (G : Graph (RoutingAlgebra.Step 𝓡𝓐) n)
  where

  open ConsistentPaths   𝓡𝓐 ⊕-sel G public renaming (size to sizeᶜ)
  open InconsistentPaths 𝓡𝓐 ⊕-sel G public renaming (size to sizeⁱ) hiding (weight; ⊕-select; sel₁; sel₂; sel≈)
  
  open RoutingAlgebra 𝓡𝓐 public
  open RoutingProblem 𝓡𝓟ᶜ public using () renaming
    ( ℝ𝕄ₛ     to ℝ𝕄ᶜₛ
    ; RMatrix  to CMatrix
    ; _≈ₘ_     to _≈ᶜₘ_
    ; _≉ₘ_     to _≉ᶜₘ_
    ; ≈ₘ-refl  to ≈ᶜₘ-refl
    ; ≈ₘ-sym   to ≈ᶜₘ-sym
    ; ≈ₘ-trans to ≈ᶜₘ-trans
    )
  open RoutingProblem 𝓡𝓟ⁱ public using () renaming
    ( ℝ𝕄ₛ     to ℝ𝕄ⁱₛ
    ; RMatrix  to IMatrix
    ; _≈ₘ_     to _≈ⁱₘ_
    ; _≉ₘ_     to _≉ⁱₘ_
    ; _≟ₘ_     to _≟ⁱₘ_
    ; ≈ₘ-refl  to ≈ⁱₘ-refl
    ; ≈ₘ-sym   to ≈ⁱₘ-sym
    ; ≈ₘ-trans to ≈ⁱₘ-trans
    )
  
  open BellmanFord 𝓡𝓟ⁱ public using () renaming (σ to σⁱ; σ-cong to σⁱ-cong; I to Iⁱ)
  open BellmanFord 𝓡𝓟ᶜ public using () renaming (σ to σᶜ; σ-cong to σᶜ-cong; I to Iᶜ)

  
  open import RoutingLib.Routing.AlgebraicPaths.Inconsistent.Properties 𝓡𝓐 ⊕-sel G public renaming
    ( size<n to sizeⁱ<n
    )
    
  open import RoutingLib.Routing.AlgebraicPaths.Consistent.Properties 𝓡𝓐 ⊕-sel G public
  
  open import RoutingLib.Routing.AlgebraicPaths.Translation 𝓡𝓐 ⊕-sel G public



  ----------------------------------------------------------------------------
  -- All paths operations preserve consistency

  Iⁱᶜ : 𝑪ₘ Iⁱ
  Iⁱᶜ i j with j ≟𝔽 i
  ... | yes _ = 𝒄-route [] refl
  ... | no  _ = 𝒄-null
    
  σⁱ-pres-𝑪ₘ : ∀ {X} → 𝑪ₘ X → 𝑪ₘ (σⁱ X)
  σⁱ-pres-𝑪ₘ Xᶜ i j = foldr-×pres {P = 𝑪} ⊕ⁱ-pres-𝑪
    (tabulate⁺ (λ k → ▷ⁱ-pres-𝑪 (Aⁱ i k) (Xᶜ k j))) (Iⁱᶜ i j)

  Iⁱ-fromI : ∀ i j → fromI (Iⁱᶜ i j) ≈ᶜ Iᶜ i j
  Iⁱ-fromI i j with j ≟𝔽 i
  ... | yes _ = ≈ᶜ-refl
  ... | no  _ = ≈ᶜ-refl

  σ-fromIₘ-commute : ∀ {X} (Xᶜ : 𝑪ₘ X) (σXᶜ : 𝑪ₘ (σⁱ X)) → fromIₘ σXᶜ ≈ᶜₘ  σᶜ (fromIₘ Xᶜ)
  σ-fromIₘ-commute {X} Xᶜ σXᶜ i j =
    foldr-fromI-commute (Iⁱᶜ i j) (Iⁱ-fromI i j) (σXᶜ i j)
      (pw-tabulate⁺ (λ k → (▷ⁱ-pres-𝑪 (Aⁱ i k) (Xᶜ k j)) , (▷-fromI-commute (Xᶜ k j) (▷ⁱ-pres-𝑪 (Aⁱ i k) (Xᶜ k j)))))
    where

    pw-tabulate⁺ : ∀ {a b ℓ} {A : Set a} {B : Set b} {_~_ : REL A B ℓ} →
                     ∀ {n} {f : Fin n → A} {g : Fin n → B} → (∀ i → f i ~ g i) →
                     ListRel _~_ (tabulate f) (tabulate g)
    pw-tabulate⁺ {n = zero} f~g  = []
    pw-tabulate⁺ {n = suc n} f~g = (f~g fzero) ∷ pw-tabulate⁺ (f~g ∘ fsuc)





  ------------------------------------------------------------------------------
  -- If an entry in the routing matrix is inconsistent then it must have an
  -- inconsistent parent route

  module _ X i j (σXᵢⱼⁱ : 𝑰 (σⁱ X i j)) where
  
    𝒊-parent : Fin n
    𝒊-parent with σXᵢⱼ≈Aᵢₖ▷Xₖⱼ⊎Iᵢⱼ 𝓡𝓟ⁱ ⊕ⁱ-sel X i j
    ... | inj₁ (k , σXᵢⱼ≈Aᵢₖ▷Xₖⱼ) = k
    ... | inj₂ σXᵢⱼ≈Iᵢⱼ           = contradiction (𝑪-cong (Iⁱᶜ i j) (≈ⁱ-sym σXᵢⱼ≈Iᵢⱼ)) σXᵢⱼⁱ
    
    𝒊-parentⁱ : 𝑰 (X 𝒊-parent j)
    𝒊-parentⁱ Xₖⱼᶜ with σXᵢⱼ≈Aᵢₖ▷Xₖⱼ⊎Iᵢⱼ 𝓡𝓟ⁱ ⊕ⁱ-sel X i j
    ... | inj₁ (k , σXᵢⱼ≈Aᵢₖ▷Xₖⱼ) = contradiction (𝑪-cong (▷ⁱ-pres-𝑪 (Aⁱ i k) Xₖⱼᶜ) (≈ⁱ-sym σXᵢⱼ≈Aᵢₖ▷Xₖⱼ)) σXᵢⱼⁱ
    ... | inj₂ σXᵢⱼ≈Iᵢⱼ           = contradiction (𝑪-cong (Iⁱᶜ i j) (≈ⁱ-sym σXᵢⱼ≈Iᵢⱼ)) σXᵢⱼⁱ

    𝒊-parent-size : sizeⁱ (σⁱ X i j) ≡ suc (sizeⁱ (X 𝒊-parent j))
    𝒊-parent-size with σXᵢⱼ≈Aᵢₖ▷Xₖⱼ⊎Iᵢⱼ 𝓡𝓟ⁱ ⊕ⁱ-sel X i j
    ... | inj₂ σXᵢⱼ≈Iᵢⱼ           = contradiction (𝑪-cong (Iⁱᶜ i j) (≈ⁱ-sym σXᵢⱼ≈Iᵢⱼ)) σXᵢⱼⁱ
    ... | inj₁ (k , σXᵢⱼ≈Aᵢₖ▷Xₖⱼ) = ▷ⁱ-size (Aⁱ i k) (X k j) (σXᵢⱼⁱ ∘ 𝑪-cong 𝒄-null ∘ ≈ⁱ-sym) σXᵢⱼ≈Aᵢₖ▷Xₖⱼ





{-

    flushing-lemma : ∀ 𝕤 {n X i j t} → pseudoperiod𝔸 𝕤 n ≤ t → size (I.δ 𝕤 t X i j) < n → ∃ λ cr → I.δ 𝕤 t X i j ≃ cr
    flushing-lemma 𝕤 {zero} _ ()
    flushing-lemma 𝕤 {suc n} {X} {i} {j} {t} tₙ₊₁ⁱ≤t |p|<n with pseudoperiod𝔸-all 𝕤 n i
    ... | (aₜᵢ , tₙ<aₜᵢ , αₜᵢ≤tₙ₊₁ , i∈αₐₜᵢ , aₜᵢ≤s⇒tₙ≤βsij) with previousActivation-all (starvationFree 𝕤) (≤-trans αₜᵢ≤tₙ₊₁ tₙ₊₁ⁱ≤t) i∈αₐₜᵢ
    ...   | (t' , aₜᵢ≤t' , t'≤t , i∈αₜ' , t'-latestActivation) with m<n⇒n≡1+o (≤-trans tₙ<aₜᵢ aₜᵢ≤t')
    ...     | (t'-1 , t'≡1+t'-1) rewrite t'≡1+t'-1 with IP.δᵗ⁺¹Xᵢⱼ≈Aᵢₖ▷δᵗXₖⱼ⊎Iᵢⱼ 𝕤 ⊕ⁱ-sel X i∈αₜ' j | IP.δ-inactiveSince 𝕤 X i t'≤t t'-latestActivation j
    ...       | inj₂ δᵗ'Xᵢⱼ≈Iᵢⱼ           | δᵗX≈δᵗ'X = C.I i j , ic+ii⇒ic (Iⁱ≃Iᶜ i j) (≈ⁱ-sym (≈ⁱ-trans δᵗX≈δᵗ'X δᵗ'Xᵢⱼ≈Iᵢⱼ))
    ...       | inj₁ (k , δᵗ'Xᵢⱼ≈Aᵢₖ▷δβₖⱼ) | δᵗX≈δᵗ'X with I.δ 𝕤 (suc t'-1) X i j | inspect (I.δ 𝕤 (suc t'-1) X i) j
    ...         | inull      | [ δt'X≡inull ] = cnull , ic+ii⇒ic nullEq (≈ⁱ-sym δᵗX≈δᵗ'X)
    ...         | iroute x p | [ δᵗ'X≡xp ] with flushing-lemma 𝕤 (<⇒≤ (aₜᵢ≤s⇒tₙ≤βsij k aₜᵢ≤t')) (≤-pred (subst (_< suc n) (≡-trans (x≈y⇒|x|≡|y| (≈ⁱ-trans δᵗX≈δᵗ'X δᵗ'Xᵢⱼ≈Aᵢₖ▷δβₖⱼ)) (▷ⁱ-size (I.δ 𝕤 (β 𝕤 (suc t'-1) i k) X k j) (≈ⁱ-sym δᵗ'Xᵢⱼ≈Aᵢₖ▷δβₖⱼ))) |p|<n))
    ...           | (cr , δβₖⱼ≃cr) = (i , k) ▷ᶜ cr ,
      (begin
        I.δ 𝕤 t X i j                                  ≈ⁱ⟨ IP.δ-inactiveSince 𝕤 X i t'≤t t'-latestActivation j ⟩
        I.δ 𝕤 (suc t'-1) X i j                         ≈ⁱ⟨ ≈ⁱ-trans (≈ⁱ-reflexive δᵗ'X≡xp) δᵗ'Xᵢⱼ≈Aᵢₖ▷δβₖⱼ ⟩
        (i , k) ▷ⁱ (I.δ 𝕤 (β 𝕤 (suc t'-1) i k) X k j)  ≃⟨ ▷-≃ (i , k) δβₖⱼ≃cr ⟩
        (i , k) ▷ᶜ cr
      ∎)
-}
