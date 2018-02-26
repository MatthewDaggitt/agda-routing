open import Data.Nat using (ℕ; zero; suc; z≤n; s≤s; _+_; _∸_; _<_; _≤_)
open import Data.Nat.Properties using (+-identityʳ; +-comm; +-assoc)
open import Data.Fin using (Fin; zero; suc)
open import Data.Fin.Properties using () renaming (_≟_ to _≟𝔽_)
open import Data.Fin.Subset using (Subset; _∈_; _∉_; _∪_)
open import Data.Fin.Dec using (_∈?_)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′; map)
open import Data.Product using (_,_; _×_; ∃; ∃₂; proj₁; proj₂)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Unary
  using (∁; Decidable; U) renaming (_∈_ to _∈ᵤ_; _∉_ to _∉ᵤ_; _⊆_ to _⊆ᵤ_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; cong; subst; refl; sym; trans; inspect; [_])
import Relation.Binary.PartialOrderReasoning as POR
import Relation.Binary.EqReasoning as EqReasoning

open import RoutingLib.Data.SimplePath
  using (SimplePath; []; _∷_∣_∣_; invalid; valid; notThere; notHere; continue)
  renaming (_∈_ to _∈ₚ_)
open import RoutingLib.Data.SimplePath.Relation.Equality
open import RoutingLib.Data.SimplePath.Relation.Subpath
open import RoutingLib.Data.SimplePath.All
  using (All; invalid; valid; []; [_,_]∷_; All-resp-≈ₚ)
open import RoutingLib.Data.SimplePath.Properties
  using (∉-resp-≈ₚ)
open import RoutingLib.Data.Fin.Subset using (size)

open import RoutingLib.Routing.Definitions
open import RoutingLib.Routing.BellmanFord.PathVector.SufficientConditions
open import RoutingLib.Routing.BellmanFord.Properties using (Iᵢᵢ≡1#; Iᵢⱼ≡0#; Iᵢⱼ≈0⊎1)
import RoutingLib.Routing.BellmanFord.PathVector.Prelude as Prelude
import RoutingLib.Routing.BellmanFord.Properties as P

module RoutingLib.Routing.BellmanFord.PathVector.ConvergenceTime
  {a b ℓ} {𝓡𝓐 : RoutingAlgebra a b ℓ}
  {n-1} {𝓡𝓟 : RoutingProblem 𝓡𝓐 (suc n-1)}
  (𝓟𝓢𝓒 : PathSufficientConditions 𝓡𝓟)
  where
  
  open Prelude 𝓟𝓢𝓒 hiding (size)

  private
    𝕋 : Set
    𝕋 = ℕ

    Node : Set
    Node = Fin n

    σXᵢⱼ≤Aᵢₖ▷Xₖⱼ : ∀ X i j k → σ X i j ≤₊ A i k ▷ X k j
    σXᵢⱼ≤Aᵢₖ▷Xₖⱼ = P.σXᵢⱼ≤Aᵢₖ▷Xₖⱼ 𝓡𝓟 ⊕-idem ⊕-assoc ⊕-comm

    
    
  module _ (X : RMatrix) (j : Fin n) where
    
    -- Node i's route remains constant after time t
    Settled : 𝕋 → Node → Set _
    Settled t i = ∀ s → σ^ (s + t) X i j ≈ σ^ t X i j

    j∈Settled₁ : j ∈ᵤ Settled 1
    j∈Settled₁ s = begin
      σ^ (s + 1) X j j  ≡⟨ cong (λ t → σ^ t X j j) (+-comm s 1) ⟩
      σ^ (1 + s) X j j  ≈⟨ σXᵢᵢ≈σYᵢᵢ (σ^ s X) X j ⟩
      σ^ 1       X j j  ∎
      where open EqReasoning S

    Settledₜ⊆Settledₛ₊ₜ : ∀ t s → Settled t ⊆ᵤ Settled (s + t)
    Settledₜ⊆Settledₛ₊ₜ t s {i} i∈Sₜ u = begin
      σ^ (u + (s + t)) X i j  ≡⟨ cong (λ t → σ^ t X i j) (sym (+-assoc u s t)) ⟩
      σ^ ((u + s) + t) X i j  ≈⟨ i∈Sₜ (u + s) ⟩
      σ^ t             X i j  ≈⟨ ≈-sym (i∈Sₜ s)  ⟩
      σ^ (s + t) X i j  ∎
      where open EqReasoning S

    Settled-alignment : ∀ {t i} → i ∈ᵤ Settled t → ∀ {k l p e⇿p i∉p} →
                        path (σ^ t X i j) ≈ₚ valid ((l , k) ∷ p ∣ e⇿p ∣ i∉p) →
                        i ≡ l × σ^ t X i j ≈ A i k ▷ σ^ t X k j × path (σ^ t X k j) ≈ₚ valid p
    Settled-alignment {t} {i} i∈Sₜ p[σXᵢⱼ]≈uv∷p
      with p[σXᵢⱼ]⇒σXᵢⱼ≈AᵢₖXₖⱼ (σ^ t X) i j (≈ₚ-trans (path-cong (i∈Sₜ 1)) p[σXᵢⱼ]≈uv∷p)
    ... | i≡l , σ¹⁺ᵗXᵢⱼ≈AᵢₖσᵗXₖⱼ , p[σᵗXₖⱼ]≈p = i≡l , ≈-trans (≈-sym (i∈Sₜ 1)) σ¹⁺ᵗXᵢⱼ≈AᵢₖσᵗXₖⱼ , p[σᵗXₖⱼ]≈p


    -- Node i's route, and all nodes along that route remain constant after time t
    Fixed : 𝕋 → Node → Set _
    Fixed t i = i ∈ᵤ Settled t × All (Settled t) (path (σ^ t X i j))

    j∈Fixed₁ : j ∈ᵤ Fixed 1
    j∈Fixed₁ = j∈Settled₁ , All-resp-≈ₚ (valid []) (≈ₚ-sym (begin
      path (σ X j j) ≈⟨ path-cong (σXᵢᵢ≈Iᵢᵢ X j) ⟩
      path (I j j)   ≡⟨ cong path (P.Iᵢᵢ≡1# 𝓡𝓟 j) ⟩
      path 1#        ≈⟨ p₁≈[] ⟩
      valid []       ∎))
      where open EqReasoning (ℙₛ n)

    Fixedₜ⊆Fixedₛ₊ₜ : ∀ t s → Fixed t ⊆ᵤ Fixed (s + t)
    Fixedₜ⊆Fixedₛ₊ₜ t s (i∈Sₜ , p∈Sₜ) = Settledₜ⊆Settledₛ₊ₜ t s i∈Sₜ  , {!!}
    
    Fixed-preds : ∀ {t i} → i ∈ᵤ Fixed t →
                  ∀ {p} → path (σ^ t X i j) ≈ₚ p → All (Fixed t) p
    Fixed-preds {t} {i} i∈Fₜ                    {invalid} _ = invalid
    Fixed-preds {t} {i} i∈Fₜ                   {valid []} _ = valid []
    Fixed-preds {t} {i} i∈Fₜ@(i∈Sₜ , ik∷p∈Sₜ) {valid ((_ , k) ∷ p ∣ _ ∣ _)} p[σᵗXᵢⱼ]≈ik∷p
      with Settled-alignment i∈Sₜ p[σᵗXᵢⱼ]≈ik∷p
    ... | refl , σᵗXᵢⱼ≈AᵢₖσᵗXₖⱼ , p[σᵗXₖⱼ]≈p with All-resp-≈ₚ ik∷p∈Sₜ p[σᵗXᵢⱼ]≈ik∷p
    ...   | (valid ([ _ , k∈Sₜ ]∷ p∈Sₜ)) with All-resp-≈ₚ (valid p∈Sₜ) (≈ₚ-sym p[σᵗXₖⱼ]≈p)
    ...     | k∈Fₜ with Fixed-preds (k∈Sₜ , k∈Fₜ) p[σᵗXₖⱼ]≈p
    ...       | valid p∈Fₜ = valid ([ i∈Fₜ , (k∈Sₜ , k∈Fₜ) ]∷ p∈Fₜ)



 


    {-

    IsFixedSet : 𝕋 → Subset n → Set ℓ
    IsFixedSet t F = ∀ {i} → i ∈ F → Fixed t i
    
    data RealPath (t : 𝕋) : SimplePath n → Set ℓ where
      invalid : RealPath t invalid
      trivial : RealPath t (valid [])
      step    : ∀ {i k p e⇿p i∉p} →
                σ^ t X i j ≈ A i k ▷ σ^ t X k j →
                RealPath t (valid p) →
                RealPath t (valid ((i , k) ∷ p ∣ e⇿p ∣ i∉p))

    RealPath? : ∀ t → Decidable (RealPath t)
    RealPath? t invalid   = yes invalid
    RealPath? t (valid x) = {!!}

    RealPath-cong : ∀ t {p q} → p ≈ₚ q → RealPath t p → RealPath t q
    RealPath-cong t invalid              = {!!}
    RealPath-cong t (valid [])           = {!!}
    RealPath-cong t (valid (refl ∷ p≈q)) = {!!}




    Real : 𝕋 → Node → Set ℓ
    Real t i = RealPath t (path (σ^ t X i j))
    
    Junk : 𝕋 → Node → Set ℓ
    Junk t i = ¬ (Real t i)

    Fixed⇒Real : ∀ {t i} → Fixed t i → Real t i
    Fixed⇒Real {zero}  {i} fixed = {!!}
    Fixed⇒Real {suc t} {i} fixed = {!!} --with σXᵢⱼ≈AᵢₖXₖⱼ⊎Iᵢⱼ 

    -}
{-
    Real-extension : ∀ {t i k} → IsFixedNode t k → Real t k →
                     σ^ (suc t) X i j ≈ A i k ▷ σ^ t X k j → Real (suc t) i
    Real-extension {t} {i} {k} kᶠ kʳ  σ¹⁺ᵗXᵢⱼ≈AᵢₖσᵗXₖⱼ = RealPath-cong (suc t) {!!} {!!}


    module _ (t : 𝕋) {F} (F-fixed : IsFixedSet t F)  where

    
      -- True weight of a path at time t
      trueWeight : SimplePath n → Route
      trueWeight p@invalid                       = weight p
      trueWeight p@(valid [])                    = weight p
      trueWeight p@(valid ((i , j) ∷ q ∣ _ ∣ _)) with i ∈? F
      ... | yes _ = weight p
      ... | no  _ = A i j ▷ trueWeight (valid q)

      junkLength : SimplePath n → ℕ
      junkLength invalid                       = 0
      junkLength (valid [])                    = 0
      junkLength (valid ((i , j) ∷ q ∣ _ ∣ _)) with i ∈? F
      ... | yes _ = 0
      ... | no  _ = junkLength (valid q)
-}
{-
      Real-extension : ∀ t i k → k ∈ F → Real t k → σ^ {!!} X i j ≈ A i k ▷ σ^ {!!} X k j → Real t i
      Real-extension t i = {!!}

      Junk? : ∀ t → Decidable (Junk t)
      Junk? = {!!}

      junk-extension : ∀ s i → Junk (suc s + t) i → ∃ λ k → Junk (s + t) k ×
                         σ^ (suc s + t) X i j ≈ A i k ▷ σ^ (s + t) X k j
      junk-extension s i iʲ with σXᵢⱼ≈Aᵢₖ▷Xₖⱼ⊎Iᵢⱼ (σ^ (s + t) X) i j
      ... | inj₂ _ = {!!}
      ... | inj₁ (k , σ¹⁺ˢ⁺ᵗXᵢⱼ≈Aᵢₖσˢ⁺ᵗXₖⱼ) = k , {!!} , σ¹⁺ˢ⁺ᵗXᵢⱼ≈Aᵢₖσˢ⁺ᵗXₖⱼ

      postulate iₘᵢₙ : Node
      --iₘᵢₙ = {!!}
    
      postulate kₘᵢₙ : Node
      -- kₘᵢₙ = {!!}

      iₘᵢₙ∉F : iₘᵢₙ ∉ F
      iₘᵢₙ∉F = {!!}

      kₘᵢₙ∈F : kₘᵢₙ ∈ F
      kₘᵢₙ∈F = {!!}

      ik-min : ∀ s h l → h ∉ F → l ∈ F →
               A iₘᵢₙ kₘᵢₙ ▷ σ^ (s + t) X kₘᵢₙ j ≤₊ A h l ▷ σ^ (s + t) X l j
      ik-min = {!!}

      junkLength<n∸|F| : ∀ s k → junkLength (path (σ^ (s + t) X k j)) < n ∸ size F
      junkLength<n∸|F| zero    k = {!!}
      junkLength<n∸|F| (suc s) k = {!!}
    
      junk-res : ∀ s → (σ^ (suc s + t) X iₘᵢₙ j ≈ A iₘᵢₙ kₘᵢₙ ▷ σ^ (s + t) X kₘᵢₙ j)
                 ⊎ (s ≤ junkLength (path (σ^ (suc s + t) X iₘᵢₙ j)))
      junk-res s with σXᵢⱼ≈Aᵢₖ▷Xₖⱼ⊎Iᵢⱼ (σ^ (s + t) X) iₘᵢₙ j
      ... | inj₂ σ¹⁺ˢ⁺ᵗXᵢⱼ≈Iᵢⱼ               = {!contradiction ? ?!}
      ... | inj₁ (l , σ¹⁺ˢ⁺ᵗXₖⱼ≈Aₖₗσˢ⁺ᵗXₗⱼ) with l ∈? F
      ...   | no  l∉F = inj₂ {!!}
      ...   | yes l∈F = inj₁ (≤₊-antisym
        (σXᵢⱼ≤Aᵢₖ▷Xₖⱼ (σ^ (s + t) X) iₘᵢₙ j kₘᵢₙ)
        (begin
          A iₘᵢₙ kₘᵢₙ ▷ σ^ (s + t) X kₘᵢₙ j ≤⟨ ik-min s iₘᵢₙ l iₘᵢₙ∉F l∈F ⟩
          A iₘᵢₙ l    ▷ σ^ (s + t) X l j   ≈⟨ ≈-sym σ¹⁺ˢ⁺ᵗXₖⱼ≈Aₖₗσˢ⁺ᵗXₗⱼ ⟩
          σ^ (suc s + t) X iₘᵢₙ j ∎))
        where open POR ≤₊-poset
      
      result : IsFixedNode (t + {!!}) iₘᵢₙ
      result zero    = ≈-refl
      result (suc s) with σXᵢⱼ≈Aᵢₖ▷Xₖⱼ⊎Iᵢⱼ (σ^ (s + t + {!!}) I) iₘᵢₙ j
      ... | inj₂ σ¹⁺ˢ⁺ᶜIᵢⱼ≈Iᵢⱼ              = {!!}
      ... | inj₁ (k , σ¹⁺ˢ⁺ᶜIᵢⱼ≈Aᵢₖσˢ⁺ᶜIₖⱼ) = {!!}

-}

{-
  proofStep : ∀ m → ∀ {F} → IsFixedSet (c m) F → IsFixedSet (c (m + 1)) F
  proofStep m = {!!}
-}
