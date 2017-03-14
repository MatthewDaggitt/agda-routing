open import Data.Nat using (suc; zero; _+_; _≤_)
open import Data.List using (List)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Fin.Properties using () renaming (_≟_ to _≟ᶠ_)
open import Data.Fin.Subset using (_∈_)
open import Data.Fin.Dec using (_∈?_)
open import Data.List.Any as Any using (satisfied)
open import Data.List.All using (All; []; _∷_; all) renaming (lookup to all-lookup)
open import Data.Vec using (Vec; tabulate; lookup; toList)
open import Data.Vec.Properties using (∈-allFin; lookup∘tabulate)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (∃; ∃₂; _,_; _×_; proj₁; proj₂)
open import Relation.Binary using (_⇒_; Setoid; Rel; Reflexive; Symmetric; Transitive; IsEquivalence; Decidable)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; cong; subst; subst₂) renaming (setoid to ≡-setoid; refl to ≡-refl; trans to ≡-trans; sym to ≡-sym)
open import Algebra.FunctionProperties using (RightIdentity; RightZero; Commutative; Associative; Selective)

open import RoutingLib.Asynchronous using (Parallelisation)
open import RoutingLib.Asynchronous.Schedule using (Schedule)
open import RoutingLib.Algebra.FunctionProperties
open import RoutingLib.Data.Vec.Properties using (lookup-map)
open import RoutingLib.Relation.Binary.RespectedBy using (_RespectedBy_)
open import RoutingLib.Routing.Definitions
open import RoutingLib.Data.Vec.All.Properties using (foldr₂-All₂; tabulate-All₂)
open import RoutingLib.Induction.Nat using () renaming (<-well-founded to <-wf)

module RoutingLib.Routing.Algorithms.BellmanFord.Properties
  {a b ℓ n} (rp : RoutingProblem a b ℓ n)
  where

  -----------
  -- Setup --
  -----------

  open RoutingProblem rp
  open import RoutingLib.Routing.Algorithms.BellmanFord rp
  open import RoutingLib.Data.Vec.SelectiveFolds S _⊕_ ⊕-pres-≈

  open import RoutingLib.Algebra.Selectivity.NaturalOrders S _⊕_ ⊕-pres-≈ using (_≤ᵣ_; ≤ᵣ-antisym; ≤ᵣ-resp-≈)
  open import Relation.Binary.NonStrictToStrict _≈_ _≤ᵣ_ using () renaming (_<_ to _<ᵣ_)


  abstract

    ---------------------
    -- Identity matrix --
    ---------------------

    Iᵢᵢ≈1# : ∀ i → I i i ≈ 1#
    Iᵢᵢ≈1# i with i ≟ᶠ i
    ... | yes _   = refl
    ... | no  i≢i = contradiction ≡-refl i≢i

    Iᵢⱼ≈0# : ∀ {i j} → j ≢ i → I i j ≈ 0#
    Iᵢⱼ≈0# {i} {j} i≢j with j ≟ᶠ i
    ... | yes i≡j = contradiction i≡j i≢j
    ... | no  _   = refl

    Iᵢⱼ≈Iₖₗ : ∀ {i j k l} → j ≢ i → l ≢ k → I i j ≈ I k l
    Iᵢⱼ≈Iₖₗ j≢i l≢k = trans (Iᵢⱼ≈0# j≢i) (sym (Iᵢⱼ≈0# l≢k))



    ----------------------------
    -- Synchronous properties --
    ----------------------------

    σ-cong : ∀ {X Y} → X ≈ₘ Y → σ X ≈ₘ σ Y
    σ-cong X≈Y i j = foldr₂-All₂ _≈_ ⊕-pres-≈ refl (tabulate-All₂ _≈_ (λ k → ▷-pres-≈ (A i k) (X≈Y k j)))

    -- σ either extends the route by going through some k or it chooses a trivial route from the identity matrix
    σXᵢⱼ≈Aᵢₖ▷Xₖⱼ⊎Iᵢⱼ : Selective _≈_ _⊕_ → ∀ X i j → (∃ λ k → σ X i j ≈ A i k ▷ X k j) ⊎ (σ X i j ≈ I i j)
    σXᵢⱼ≈Aᵢₖ▷Xₖⱼ⊎Iᵢⱼ ⊕-sel X i j with ∃-foldr ⊕-sel (I i j) (tabulate (λ k → A i k ▷ X k j))
    ... | inj₁ (k , σXᵢⱼ≈extₖ) = inj₁ (k , (trans σXᵢⱼ≈extₖ (reflexive (lookup∘tabulate _ k))))
    ... | inj₂ σXᵢⱼ≈Iᵢⱼ  = inj₂ σXᵢⱼ≈Iᵢⱼ

    -- Under the following assumptions about ⊕, A▷ₘ always chooses the "best" option with respect to ⊕
    σXᵢⱼ≤Aᵢₖ▷Xₖⱼ : Selective _≈_ _⊕_ → Commutative _≈_ _⊕_ → Associative _≈_ _⊕_ → ∀ X i j k → σ X i j ≤ᵣ A i k ▷ X k j
    σXᵢⱼ≤Aᵢₖ▷Xₖⱼ ⊕-sel ⊕-comm ⊕-assoc X i j k = trans (⊕-pres-≈ (sym (reflexive (lookup∘tabulate _ k))) refl) (foldrₓₛ≤xsᵢ ⊕-sel ⊕-comm ⊕-assoc (I i j) (tabulate (λ k → A i k ▷ X k j)) k)

    -- After an iteration, the diagonal of the RMatrix is always the identity
    σXᵢᵢ≈Iᵢᵢ : Selective _≈_ _⊕_ → Associative _≈_ _⊕_ → Commutative _≈_ _⊕_ → RightZero _≈_ 1# _⊕_ → ∀ X i → σ X i i ≈ I i i
    σXᵢᵢ≈Iᵢᵢ ⊕-sel ⊕-assoc ⊕-comm 1#-anᵣ-⊕ X i with σXᵢⱼ≈Aᵢₖ▷Xₖⱼ⊎Iᵢⱼ ⊕-sel X i i
    ... | inj₂ σXᵢᵢ≈Iᵢᵢ = σXᵢᵢ≈Iᵢᵢ
    ... | inj₁ (k , σXᵢᵢ≈AᵢₖXₖⱼ) = ≤ᵣ-antisym ⊕-comm (foldrₑ≤e ⊕-sel ⊕-comm ⊕-assoc (I i i) (tabulate (λ k → A i k ▷ X k i))) (≤ᵣ-resp-≈ (sym (Iᵢᵢ≈1# i)) (sym (trans σXᵢᵢ≈AᵢₖXₖⱼ refl)) (1#-anᵣ-⊕ (A i k ▷ X k i)))

    -- After an iteration, the diagonals of any two RMatrices are equal
    σXᵢᵢ≈σYᵢᵢ : Selective _≈_ _⊕_ → Associative _≈_ _⊕_ → Commutative _≈_ _⊕_ → RightZero _≈_ 1# _⊕_ → ∀ X Y i → σ X i i ≈ σ Y i i
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


    -----------------------------
    -- Asynchronous properties --
    -----------------------------

    module _ (𝕤 : Schedule n) where

      open Schedule 𝕤
      open Parallelisation σ∥ using (δ')
    
      open import RoutingLib.Asynchronous.Properties σ∥ using (δ-activated; δ-unactivated)

      δ-constantSinceActivation : ∀ X i {t t'} → t' ≤ t → (∀ {t''} → t'' ≤ t → i ∈ α t'' → t'' ≤ t') → ∀ j → δ 𝕤 t X i j ≈ δ 𝕤 t' X i j
      δ-constantSinceActivation X i t'≤t t'-latest = δ-unactivated σ-cong 𝕤 X i t'≤t t'-latest 

      δᵗ⁺¹Xᵢⱼ≈Aᵢₖ▷δᵗXₖⱼ⊎Iᵢⱼ : Selective _≈_ _⊕_ → ∀ {t} X {i} → i ∈ α (suc t) → ∀ j → (∃ λ k → δ 𝕤 (suc t) X i j ≈ A i k ▷ δ 𝕤 (β (suc t) i k) X k j) ⊎ (δ 𝕤 (suc t) X i j ≈ I i j)
      δᵗ⁺¹Xᵢⱼ≈Aᵢₖ▷δᵗXₖⱼ⊎Iᵢⱼ ⊕-sel {t} X {i} i∈α₁₊ₜ j with δ-activated σ-cong 𝕤 X t i∈α₁₊ₜ | σXᵢⱼ≈Aᵢₖ▷Xₖⱼ⊎Iᵢⱼ ⊕-sel (λ k → δ 𝕤 (β (suc t) i k) X k) i j
      ... | δ¹⁺ᵗXᵢ≈σᵇXₖ | inj₁ (k , σᵇXᵢⱼ≈Aᵢₖ▷δᵇXₖⱼ) = inj₁ (k , trans (δ¹⁺ᵗXᵢ≈σᵇXₖ j) σᵇXᵢⱼ≈Aᵢₖ▷δᵇXₖⱼ)
      ... | δ¹⁺ᵗXᵢ≈σᵇXₖ | inj₂ σᵇXᵢⱼ≈Iᵢⱼ            = inj₂ (trans (δ¹⁺ᵗXᵢ≈σᵇXₖ j) σᵇXᵢⱼ≈Iᵢⱼ)

  --σXᵢⱼ≈Aᵢₖ▷Xₖⱼ⊎Iᵢⱼ ⊕-sel X i j with ∃-foldr ⊕-sel (I i j) (extensions X i j)
  --... | inj₁ (k , σXᵢⱼ≈extₖ) = inj₁ (k , (trans σXᵢⱼ≈extₖ (reflexive (lookup-extensions X i j k))))
  --... | inj₂ σXᵢⱼ≈Iᵢⱼ  = inj₂ σXᵢⱼ≈Iᵢⱼ

