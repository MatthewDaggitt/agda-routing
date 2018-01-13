open import Data.Fin using (Fin)
open import Data.Nat using (ℕ; _≤_; _<_; suc; _+_) renaming (_≟_ to _≟ℕ_)
open import Data.Nat.Properties using (≤-decTotalOrder; _<?_)
open import Data.List using (List; length)
open import Data.List.Any.Membership.Propositional using () renaming (_∈_ to _∈ℕ_)
open import Data.Vec using (Vec; fromList)
open import Data.Product using (∃)
open import Relation.Binary using (Setoid; Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Nullary using (yes; no)

open import RoutingLib.Data.Nat.Properties using (ℕₛ)
open import RoutingLib.Data.List using (index)
open import RoutingLib.Data.List.Membership.DecPropositional _≟ℕ_ using (deduplicate)
open import RoutingLib.Data.List.Membership.DecPropositional.Properties
  using (∈-deduplicate⁻; ∈-deduplicate⁺)
open import RoutingLib.Data.List.Sorting.Mergesort ≤-decTotalOrder
open import RoutingLib.Data.List.Sorting ≤-decTotalOrder using (Sorted)
open import RoutingLib.Data.List.Uniqueness.Propositional using (Unique)
open import RoutingLib.Data.List.Uniqueness.Propositional.Properties using (deduplicate!⁺)
open import RoutingLib.Asynchronous using (Parallelisation)
open import RoutingLib.Asynchronous.Theorems using (ACO; UltrametricConditions)
open import RoutingLib.Function.Image using (FiniteImage)

module RoutingLib.Asynchronous.Theorems.MetricToBox
  {a ℓ n} {S : Fin n → Setoid a ℓ} {P : Parallelisation S}
  (𝓤𝓒 : UltrametricConditions P) where

    open Parallelisation P using (M; f; Pred; _⊂_; _≈_; _∈_; Singleton-t)
    open UltrametricConditions 𝓤𝓒


    postulate x* : M
    
    open FiniteImage (d-finiteImage x*)



    -- Radii in list form
    
    radiiₗ : List ℕ
    radiiₗ = mergesort (deduplicate image)

    radiiₗ↗ : Sorted radiiₗ
    radiiₗ↗ = mergesort↗ (deduplicate image)
    
    radiiₗ! : Unique radiiₗ
    radiiₗ! = mergesort!⁺ (deduplicate!⁺ _≟ℕ_ image)

    radiiₗ-complete : ∀ x → d x* x ∈ℕ radiiₗ
    radiiₗ-complete x = ∈-mergesort⁺ (∈-deduplicate⁺ _≟ℕ_ (complete x))

    radiiₗ-sound : ∀ {r} → r ∈ℕ radiiₗ → ∃ λ x → d x* x ≡ r
    radiiₗ-sound r∈radii = sound (∈-deduplicate⁻ _≟ℕ_ (∈-mergesort⁻ r∈radii))


    -- Total number of radii
    
    T : ℕ
    T = length radiiₗ

    -- Boxes

    D : ℕ → Pred {!!}
    D t i m = ? -- d x* {!!} ≤ {!!}

{-
    D-decreasing : ∀ K → K < T → D (suc K) ⊂ D K
    D-decreasing = {!!}
    
    D-finish     : ∃ λ ξ → ∀ K → Singleton-t ξ (D (T + K))
    D-finish = {!!}
    
    f-monotonic  : ∀ K {t} → t ∈ D K → f t ∈ D (suc K)
    f-monotonic = {!!}
    
    D-subst : ∀ K {x y} → x ≈ y → x ∈ D K → y ∈ D K
    D-subst = {!!}

    --open IsUltrametric d-isUltrametric

    -- Given the finite image of d we can create a sorted list of the values d can take. These are the radii of the balls in the ultrametric space.
-}
{-
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


    aco : ACO P {!!}
    aco = record
      { T            = T
      ; D            = D
      ; D-decreasing = D-decreasing
      ; D-finish     = D-finish
      ; f-monotonic  = f-monotonic
      ; D-subst      = D-subst
      }
-}
