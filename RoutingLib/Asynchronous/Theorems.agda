open import Level using (Level; _⊔_) renaming (zero to lzero; suc to lsuc)
open import Data.Nat using (ℕ; _+_; _∸_; _<_; _≤_; z≤n; zero; suc; _≟_)
open import Data.Nat.Properties using (≰⇒>; module ≤-Reasoning; ≤-decTotalOrder; ≤-refl; ≤-trans; <⇒≤; <-irrefl; <-transˡ; <-asym; <⇒≱; ≮⇒≥)
open import Data.Fin using (Fin; pred; fromℕ; inject₁) renaming (_<_ to _<𝔽_; _≤_ to _≤𝔽_; _≤?_ to _≤𝔽?_; zero to fzero; suc to fsuc)
open import Data.Fin.Properties using () renaming (_≟_ to _≟𝔽_) renaming (_<?_ to _<𝔽?_)
open import Data.Product using (∃; _×_; _,_; proj₂)
open import Data.List using (List; length)
open import Data.List.Any.Membership.Propositional using (_∈_)
open import Data.Vec using (Vec; lookup; fromList) renaming (_∈_ to _∈ᵥ_)
open import Data.Vec.Properties using (List-∈⇒∈)
open import Relation.Binary using (Setoid; Decidable; _Preserves₂_⟶_⟶_)
open import Relation.Unary using (Pred) renaming (_∈_ to _∈ᵤ_; _⊆_ to _⊆ᵤ_)
open import Relation.Binary.PropositionalEquality using (_≡_; subst; cong; module ≡-Reasoning) renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans; setoid to ≡-setoid)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Function using (_∘_)

open import RoutingLib.Asynchronous
open import RoutingLib.Relation.Unary using () renaming (_⊂_ to _⊂ᵤ_; _⊈_ to _⊈ᵤ_)
open import RoutingLib.Data.Nat.Properties using (n≤0⇒n≡0)
open import RoutingLib.Data.Fin.Properties using (≤fromℕ; ≤+≢⇒<; <⇒≤pred)
open import RoutingLib.Data.List.All using (AllPairs)
open import RoutingLib.Data.List using (max)
open import RoutingLib.Data.List.Any.Membership.Propositional using (∈-length)
open import RoutingLib.Data.List.Sorting ≤-decTotalOrder using (sort; sort-Sorted; sort-↗)
open import RoutingLib.Data.List.Sorting.Properties ≤-decTotalOrder using (↗-unique; ↗-length; ↗-∈ˡ; ↗-∈ʳ)
open import RoutingLib.Data.List.Sorting.Nat using (strictlySorted)
open import RoutingLib.Data.List.Uniqueness using (Unique)
open import RoutingLib.Data.Vec.Properties using (∈-lookup; ∈-fromList⁻; ∈-lookup⁺)
open import RoutingLib.Data.Vec.All.Properties using (AllPairs-lookup; AllPairs-fromList⁺)

module RoutingLib.Asynchronous.Theorems {a ℓ n} {S : Setoid a ℓ} (p : Parallelisation S n) where

  open Parallelisation p
  open import RoutingLib.Asynchronous.Properties p
  open import RoutingLib.Function.Distance (Sₘ n)
  open import RoutingLib.Function.Distance.Properties (Sₘ n) using (x*; x*-fixed)

  record BoxConditions : Set (a ⊔ lsuc lzero) where
    field
      k            : ℕ
      
      C            : Fin (suc k) → Pred M lzero

      Cₖ≡M         : ∀ m      → m ∈ᵤ C (fromℕ k)
      C-strictMono : ∀ {r s}  → r <𝔽 s → C r ⊂ᵤ C s
      σ-dec        : ∀ {m r} → m ∈ᵤ C r → σ m ∈ᵤ C (pred r)


  postulate BoxConditions⇒AsynchronouslySafe : BoxConditions → IsAsynchronouslySafe p

  postulate AsynchronouslySafe⇒BoxConditions : IsAsynchronouslySafe p → BoxConditions






  record UltrametricConditions : Set (a ⊔ ℓ) where
    field
      d                  : M → M → ℕ
      d-isUltrametric    : IsUltrametric d
      d-cong             : d Preserves₂ _≈ₘ_ ⟶ _≈ₘ_ ⟶ _≡_
      σ-strContr-d       : σ StrContrOver d
      m*                 : M
      m*-fixed           : σ m* ≈ₘ m*
      m*-image           : List ℕ
      m*-image!          : Unique (≡-setoid ℕ) m*-image
      m*-image-complete  : ∀ x → d x m* ∈ m*-image
      m*-image-sound     : ∀ {i} → i ∈ m*-image → ∃ λ x → d x m* ≡ i 
      



  module Ultrametric⇒Box (_≟ₘ_ : Decidable (_≈ₘ_ {n})) (uc : UltrametricConditions) where

    open UltrametricConditions uc
    open IsUltrametric d-isUltrametric

    -- Given the finite image of d we can create a sorted list of the values d can take. These are the radii of the balls in the ultrametric space.


    -- The index of the largest ball we are going to construct
    k : ℕ
    k = length m*-image ∸ 1

    1+k≡|sortedImage| : suc k ≡ length (sort m*-image)
    1+k≡|sortedImage| with ∈-length (m*-image-complete m*)
    ... | (n , |i|≡1+n) = ≡-trans (cong (λ v → suc (v ∸ 1)) |i|≡1+n) (≡-trans (≡-sym |i|≡1+n) (↗-length (sort-↗ m*-image)))


    -- A vector of the radii sorted in ascending order

    radii : Vec ℕ (suc k)
    radii rewrite 1+k≡|sortedImage| = fromList (sort m*-image)

    radii-mono-< : ∀ {i j} → i <𝔽 j → lookup i radii < lookup j radii
    radii-mono-< i<j rewrite 1+k≡|sortedImage| = AllPairs-lookup (AllPairs-fromList⁺ (strictlySorted (sort-Sorted m*-image) (↗-unique m*-image! (sort-↗ m*-image)))) i<j
    
    radii-mono-≤ : ∀ {i j} → i ≤𝔽 j → lookup i radii ≤ lookup j radii
    radii-mono-≤ {i} {j} i≤j with i ≟𝔽 j
    ... | yes ≡-refl = ≤-refl
    ... | no  i≢j    = <⇒≤ (radii-mono-< (≤+≢⇒< i≤j i≢j))
    
    radii-mono-≤-inv : ∀ {i j} → lookup j radii < lookup (fsuc i) radii → j ≤𝔽 (inject₁ i)
    radii-mono-≤-inv {i} {j} radiiⱼ<radii₁₊ᵢ with j <𝔽? fsuc i
    ... | yes j<1+i = <⇒≤pred j<1+i
    ... | no  j≮1+i = contradiction (radii-mono-≤ (≮⇒≥ j≮1+i)) (<⇒≱ radiiⱼ<radii₁₊ᵢ)
    
    radii-complete : ∀ x → ∃ λ i → lookup i radii ≡ d x m* 
    radii-complete x rewrite 1+k≡|sortedImage| = ∈-lookup (List-∈⇒∈ (↗-∈ˡ (m*-image-complete x) (sort-↗ m*-image)))

    radii-sound : ∀ i → ∃ λ x → d x m* ≡ lookup i radii
    radii-sound i rewrite 1+k≡|sortedImage| = m*-image-sound (↗-∈ʳ (∈-fromList⁻ (∈-lookup⁺ i (fromList (sort m*-image)))) (sort-↗ m*-image))



    -- The set of boxes

    C : Fin (suc k) → Pred M lzero
    C i = _∈[ d ∥ m* , lookup i radii ]


    -- Every element is contained in the outermost box

    Cₖ≡M : ∀ m → m ∈ᵤ C (fromℕ k)
    Cₖ≡M m with radii-complete m
    ... | (i , radiiᵢ≡dm⋆x) rewrite ≡-sym radiiᵢ≡dm⋆x = radii-mono-≤ (≤fromℕ k i)


    -- Each subsequent box is strictly contained inside of it's predecessor
    
    Cₛ⊆Cᵣ⇒radiiₛ≤radiiᵣ : ∀ {r s} → C s ⊆ᵤ C r → lookup s radii ≤ lookup r radii
    Cₛ⊆Cᵣ⇒radiiₛ≤radiiᵣ {r} {s} Cₛ⊆Cᵣ rewrite ≡-sym (proj₂ (radii-sound s)) = Cₛ⊆Cᵣ ≤-refl

    C-strictMono-⊆ : ∀ {r s} → r <𝔽 s → C r ⊆ᵤ C s
    C-strictMono-⊆ r<s x∈Cᵣ = ≤-trans x∈Cᵣ (<⇒≤ (radii-mono-< r<s))
 
    C-strictMono-⊉ : ∀ {r s} → r <𝔽 s → C s ⊈ᵤ C r
    C-strictMono-⊉ {r} {s} r<s Cₛ⊆Cᵣ = <-irrefl ≡-refl (<-transˡ (radii-mono-< r<s) (Cₛ⊆Cᵣ⇒radiiₛ≤radiiᵣ {r} {s} Cₛ⊆Cᵣ))

    C-strictMono : ∀ {r s} → r <𝔽 s → C r ⊂ᵤ C s
    C-strictMono r<s = C-strictMono-⊆ r<s , C-strictMono-⊉ r<s
    

    -- Applying σ is guaranteed to take you to a smaller box

    σ-dec≈ : ∀ {m} → m ≈ₘ m* → ∀ i → σ m ∈ᵤ C i
    σ-dec≈ {m} m≈m* i =
      begin
        d (σ m) m*            ≡⟨ d-cong (σ-cong m≈m*) ≈ₘ-refl ⟩
        d (σ m*) m*           ≡⟨ eq⇒0 m*-fixed ⟩
        zero                  ≤⟨ z≤n ⟩
        lookup i radii
      ∎
      where open ≤-Reasoning

    σ-dec₀ : ∀ {m} → m ≉ₘ m* → m ∈ᵤ C fzero → σ m ∈ᵤ C fzero
    σ-dec₀ {m} m≉m* m∈C₀ = 
      begin
        d (σ m) m*            ≡⟨ d-cong ≈ₘ-refl (≈ₘ-sym m*-fixed) ⟩
        d (σ m) (σ m*)        ≤⟨ <⇒≤ (σ-strContr-d (m≉m* ∘ ≈ₘ-sym)) ⟩
        d m m*                ≤⟨ m∈C₀ ⟩
        lookup fzero radii
      ∎
      where open ≤-Reasoning
      
    σ-decᵢ₊₁ : ∀ {m} → m ≉ₘ m* → ∀ {i} → m ∈ᵤ C (fsuc i) → σ m ∈ᵤ C (inject₁ i)
    σ-decᵢ₊₁ {m} m≉m* {i} m∈C₁₊ᵢ with radii-complete (σ m)
    ... | (j , radiiⱼ≡dσmm*) = subst (_≤ lookup (inject₁ i) radii) radiiⱼ≡dσmm* (radii-mono-≤ {j} {inject₁ i} (radii-mono-≤-inv (
      begin
        suc (lookup j radii) ≡⟨ cong suc radiiⱼ≡dσmm* ⟩
        suc (d (σ m) m*)     ≡⟨ cong suc (d-cong ≈ₘ-refl (≈ₘ-sym m*-fixed)) ⟩
        suc (d (σ m) (σ m*)) ≤⟨ σ-strContr-d (m≉m* ∘ ≈ₘ-sym) ⟩
        d m m*               ≤⟨ m∈C₁₊ᵢ ⟩
        lookup (fsuc i) radii
      ∎)))
      where open ≤-Reasoning


    σ-dec : ∀ {m i} → m ∈ᵤ C i → σ m ∈ᵤ C (pred i)
    σ-dec {m} {i} m∈Cᵢ with m ≟ₘ m*
    σ-dec {_} {i}      m∈Cᵢ   | yes m≈m* = σ-dec≈ m≈m* (pred i)
    σ-dec {_} {fzero}  m∈C₀  | no m≉m*  = σ-dec₀ m≉m* m∈C₀
    σ-dec {_} {fsuc i} m∈C₁₊ᵢ | no m≉m* = σ-decᵢ₊₁ m≉m* m∈C₁₊ᵢ


    -- Hence we have the required box conditions

    boxConditions : BoxConditions
    boxConditions = record
      { k = k
      ; C = C
      ; Cₖ≡M = Cₖ≡M
      ; C-strictMono = C-strictMono
      ; σ-dec = λ {m} {i} → σ-dec {m} {i}
      }
