open import Data.Nat using (suc; zero; _+_)
open import Data.List using (List)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Fin.Properties using () renaming (_≟_ to _≟ᶠ_)
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

open import RoutingLib.Algebra.FunctionProperties
open import RoutingLib.Data.Vec.Properties using (lookup-map)
open import RoutingLib.Relation.Binary.RespectedBy using (_RespectedBy_)
open import RoutingLib.Routing.Definitions

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

{-
    Iᵢⱼ-idᵣ-⊕ : ∀ {i j} → j ≢ i → RightIdentity _≈_ (I i j) _⊕_
    Iᵢⱼ-idᵣ-⊕ {i} {j} j≢i x = trans (⊕-pres-≈ refl (Iᵢⱼ≈0# j≢i)) (0#-idᵣ-⊕ x)

    Iᵢⱼ-idₗ-⊕ : ∀ {i j} → j ≢ i → LeftIdentity _≈_ (I i j) _⊕_
    Iᵢⱼ-idₗ-⊕ {i} {j} j≢i x = trans (⊕-comm (I i j) x) (Iᵢⱼ-idᵣ-⊕ j≢i x)

    Iᵢⱼ-anᵣ-▷ : ∀ {i j} → j ≢ i → ∀ s → s ▷ I i j ≈ I i j
    Iᵢⱼ-anᵣ-▷ j≢i s = trans (trans (▷-pres-≈ s (Iᵢⱼ≈0# j≢i)) (0#-anᵣ-▷ s)) (sym (Iᵢⱼ≈0# j≢i))
-}

    Iᵢⱼ≈Iₖₗ : ∀ {i j k l} → j ≢ i → l ≢ k → I i j ≈ I k l
    Iᵢⱼ≈Iₖₗ j≢i l≢k = trans (Iᵢⱼ≈0# j≢i) (sym (Iᵢⱼ≈0# l≢k))

    ---------------------
    -- Properties of σ --
    ---------------------

    -- Applying σ no times is equivalent to the identity function
    σ⁰X≡X : ∀ X → σ^ zero X ≡ X
    σ⁰X≡X _ = ≡-refl

{-
    -- σ addition
    σᵐ⁺ⁿ≡σᵐσⁿ : ∀ m n X → σ^ (m + n) X ≡ σ^ m (σ^ n X)
    σᵐ⁺ⁿ≡σᵐσⁿ zero    _ _ = ≡-refl
    σᵐ⁺ⁿ≡σᵐσⁿ (suc m) n X = {!cong σ ?!}
-}

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





{-




  t≡s⇒δ'ᵗᵢⱼ≡δ'ˢᵢⱼ : ∀ X i j {s t} → s ≡ t → (tAcc : Acc _<_ t) → (sAcc : Acc _<_ s) → δ' tAcc X i j ≡ δ' sAcc X i j
  t≡s⇒δ'ᵗᵢⱼ≡δ'ˢᵢⱼ X i j {zero}  ≡-refl (acc tAcc) (acc sAcc) = ≡-refl
  t≡s⇒δ'ᵗᵢⱼ≡δ'ˢᵢⱼ X i j {suc t} ≡-refl (acc tAcc) (acc sAcc) with i ∈? α (suc t)
  ... | yes _ = cong (foldr (λ _ → Route) _⊕_ (I i j))
                  (map-cong (λ k → cong (A i k ▷_) (t≡s⇒δ'ᵗᵢⱼ≡δ'ˢᵢⱼ X k j ≡-refl (tAcc (β (suc t) i k) (causality t i k)) (sAcc (β (suc t) i k) (causality t i k)))) (allFin n))
  ... | no  _ = t≡s⇒δ'ᵗᵢⱼ≡δ'ˢᵢⱼ X i j ≡-refl (tAcc t ≤-refl) (sAcc t ≤-refl)

  postulate δ'ᵢ-constantSincePreviousActivation : ∀ {t aₜ} X i j → (tAcc : Acc _<_ t) → (aₜ≤t : aₜ ≤ t) → (i∈αₐₜ : i ∈ α aₜ) → (prevAcc : Acc _<_ (previousActivation aₜ≤t i∈αₐₜ)) → δ' tAcc X i j ≈ δ' prevAcc X i j
  {-
  δᵢ-constantSincePreviousActivation {zero}  {zero}  X i j _ 0≤0 i∈α₀ _ rewrite n≤0⇒n≡0 (previousActivation-before 0≤0 i∈α₀) = refl
  δᵢ-constantSincePreviousActivation {zero}  {suc aₜ} X i j _ ()
  δᵢ-constantSincePreviousActivation {suc t} {aₜ}     X i j (acc tAcc) aₜ≤t+1 i∈αₐₜ (acc prevAcc) with previousActivation aₜ≤t+1 i∈αₐₜ | inspect (previousActivation aₜ≤t+1) i∈αₐₜ
  δᵢ-constantSincePreviousActivation {suc t} {aₜ}     X i j (acc tAcc) aₜ≤t+1 i∈αₐₜ (acc prevAcc) | zero | [ pa≡0 ] with i ∈? α (suc t)
  ...   | yes _ = {!!}
  ...   | no  _ = {!δᵢ-constantSincePreviousActivation X i j ? ? ? ?!}
  δᵢ-constantSincePreviousActivation {suc t} {aₜ}     X i j (acc tAcc) aₜ≤t+1 i∈αₐₜ (acc prevAcc) | suc prevAct | _ = {!!}
  -}

  postulate δᵢ-latestActivation : ∀ {t t'} X i j → (∀ {t''} → t'' ≤ t → i ∈ α t'' → t'' ≤ t') →  δ t X i j ≈ δ t' X i j
  --δᵢ-constantSinceLatestActivation {t} {aₜ} X i j t'-latest = {!!} --δ'ᵢ-constantSincePreviousActivation X i j (<-wf t) aₜ≤t i∈αₐₜ (<-wf (previousActivation aₜ≤t i∈αₐₜ))





  postulate δᵗ⁺¹Xᵢⱼ≈Aᵢₖ▷δᵗXₖⱼ⊎Iᵢⱼ : Selective _≈_ _⊕_ → ∀ {t} X i j → i ∈ α (suc t) → (∃ λ k → δ (suc t) X i j ≈ A i k ▷ δ (β (suc t) i k) X k j) ⊎ (δ (suc t) X i j ≈ I i j)

  --σXᵢⱼ≈Aᵢₖ▷Xₖⱼ⊎Iᵢⱼ ⊕-sel X i j with ∃-foldr ⊕-sel (I i j) (extensions X i j)
  --... | inj₁ (k , σXᵢⱼ≈extₖ) = inj₁ (k , (trans σXᵢⱼ≈extₖ (reflexive (lookup-extensions X i j k))))
  --... | inj₂ σXᵢⱼ≈Iᵢⱼ  = inj₂ σXᵢⱼ≈Iᵢⱼ



{-
  with suc t ≟ℕ aₜ
  ... | yes t+1≡aₜ | yes i∈αₜ₊₁ = {!!}
  ... | yes t+1≡aₜ | no  i∉αₜ₊₁ = {!!} --reflexive (t≡s⇒δ'ᵗᵢⱼ≡δ'ˢᵢⱼ X i j {!t+1≡aₜ!} {!!} {!!})
  ... | no  t+1≢aₜ | yes i∈αₜ₊₁ = {!!}
  ... | no  t+1≢aₜ | no  i∉αₜ₊₁ = {!!} ---constantSincePreviousActivation X {!i!} {!!} {!!} {!!} {!!} {!!}
-}
-}
