
open import Data.Nat using (suc; zero; _+_)
open import Data.List using (List)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Fin.Properties using ()
open import Data.List.Any as Any using (satisfied)
open import Data.List.All using (All; []; _∷_; all) renaming (lookup to all-lookup)
open import Data.Vec using (Vec; allFin; lookup; toList)
open import Data.Vec.Properties using (lookup-allFin; ∈-allFin)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (∃; ∃₂; _,_; _×_; proj₁; proj₂)
open import Relation.Binary using (_⇒_; Setoid; Rel; Reflexive; Symmetric; Transitive; IsEquivalence; Decidable)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; cong; subst; subst₂) renaming (setoid to ≡-setoid; refl to ≡-refl; trans to ≡-trans; sym to ≡-sym)
open import Algebra.FunctionProperties using (RightIdentity; Commutative; Associative)

open import RoutingLib.Algebra.FunctionProperties
open import RoutingLib.Data.List.All.Properties as AllProperties using (¬All→Any¬)
open import RoutingLib.Data.Vec using (allPairs)
open import RoutingLib.Data.Vec.Properties using (lookup-map; ∈-allPairs)
open import RoutingLib.Relation.Binary.RespectedBy using (_RespectedBy_)
open import RoutingLib.Routing.Definitions

open import RoutingLib.Routing.Algorithms.DistributedBellmanFord.ConvergenceConditions using (ConvergenceConditions)

module RoutingLib.Routing.Algorithms.DistributedBellmanFord.Properties 
  {a b ℓ n} 
  (rp : RoutingProblem a b ℓ n)
  where

  
  -----------
  -- Setup --
  -----------

  open RoutingProblem rp
  open import RoutingLib.Routing.Algorithms.DistributedBellmanFord rp
  open import RoutingLib.Data.Vec.SelectiveFolds S _⊕_ ⊕-pres-≈
  open Any.Membership (≡-setoid (Fin n × Fin n)) using (_∈_)
  open import RoutingLib.Data.List.Any.GenericMembership (≡-setoid (Fin n × Fin n)) using (toList-preserves-∈)
  open AllProperties.SetoidProperties (≡-setoid (Fin n × Fin n)) using (∈-All)

  open import RoutingLib.Algebra.Selectivity.NaturalOrders S _⊕_ ⊕-pres-≈ using (_≤ᵣ_; ≤ᵣ-antisym; ≤ᵣ-resp-≈)
  open import Relation.Binary.NonStrictToStrict _≈_ _≤ᵣ_ using () renaming (_<_ to _<ᵣ_)



  -------------------------
  -- Source/destinations --
  -------------------------
  
  allNodes : Vec (Fin n) n
  allNodes = allFin n

  srcDstPairs : List (Fin n × Fin n)
  srcDstPairs = toList (allPairs allNodes allNodes)

  ∈-srcDstPairs : ∀ (p : Fin n × Fin n) → p ∈ srcDstPairs
  ∈-srcDstPairs (i , j) = toList-preserves-∈ (∈-allPairs allNodes allNodes (∈-allFin i) (∈-allFin j)) 


  abstract

    lookup-extensions : ∀ X i j k → lookup k (extensions X i j) ≡ A i k ▷ X k j
    lookup-extensions X i j k = ≡-trans (lookup-map k (allFin n)) (cong (λ v → A i v ▷ X v j) (lookup-allFin k))

    --------------
    -- Equality --
    --------------

    ≉-sym : Symmetric _≉_
    ≉-sym x≉y y≈x = x≉y (sym y≈x)

    -- Matrix inequality

    ≉ₘ-sym : Symmetric _≉ₘ_
    ≉ₘ-sym A≉B = λ B≈A → A≉B (λ i j → sym (B≈A i j))

    ≉ₘ-witness : ∀ {X Y} → X ≉ₘ Y → ∃₂ λ i j → ¬ (X i j ≈ Y i j)
    ≉ₘ-witness {X} {Y} X≉Y with (all (λ {(i , j) → X i j ≟ Y i j})) srcDstPairs
    ... | yes all  = contradiction (λ i j → all-lookup all (∈-srcDstPairs (i , j))) X≉Y
    ... | no  ¬all with satisfied (¬All→Any¬ (λ {(i , j) → X i j ≟ Y i j}) ¬all)
    ...   | (i , j) , y = i , j , y

    -- Matrix equality
  
    ≈ₘ-reflexive : _≡_ ⇒ _≈ₘ_
    ≈ₘ-reflexive ≡-refl i j = reflexive ≡-refl

    ≈ₘ-refl : Reflexive _≈ₘ_
    ≈ₘ-refl i j = refl

    ≈ₘ-sym : Symmetric _≈ₘ_
    ≈ₘ-sym A≈B i j = sym (A≈B i j)

    ≈ₘ-trans : Transitive _≈ₘ_
    ≈ₘ-trans A≈B B≈C i j = trans (A≈B i j) (B≈C i j)

    _≟ₘ_ : Decidable _≈ₘ_
    X ≟ₘ Y with (all (λ {(i , j) → X i j ≟ Y i j})) srcDstPairs
    ... | yes all  = yes (λ i j → all-lookup all (∈-srcDstPairs (i , j)))
    ... | no  ¬all = no (λ {X≈Y → ¬all (∈-All srcDstPairs (λ {v} _ → X≈Y (proj₁ v) (proj₂ v)))})

    ≈ₘ-isEquivalence : IsEquivalence _≈ₘ_
    ≈ₘ-isEquivalence = record { 
        refl = ≈ₘ-refl ; 
        sym = ≈ₘ-sym ; 
        trans = ≈ₘ-trans 
      }

  Sₘ : Setoid b ℓ
  Sₘ = record { 
      Carrier = RMatrix ; 
      _≈_ = _≈ₘ_ ; 
      isEquivalence = ≈ₘ-isEquivalence 
    }

    

  abstract

    ---------------------
    -- Properties of σ --
    ---------------------

    -- Applying σ no times is equivalent to the identity function
    σ⁰X≡X : ∀ X → σ^ zero X ≡ X
    σ⁰X≡X _ = ≡-refl

    -- σ addition
    σᵐ⁺ⁿ≡σᵐσⁿ : ∀ m n X → σ^ (m + n) X ≡ σ^ m (σ^ n X)
    σᵐ⁺ⁿ≡σᵐσⁿ zero    _ _ = ≡-refl
    σᵐ⁺ⁿ≡σᵐσⁿ (suc m) n X = cong σ (σᵐ⁺ⁿ≡σᵐσⁿ m n X)

    -- σ either extends the route by going through some k or it chooses a trivial route from the identity matrix
    σXᵢⱼ≈Aᵢₖ▷Xₖⱼ⊎Iᵢⱼ : Selective _≈_ _⊕_ → ∀ X i j → (∃ λ k → σ X i j ≈ A i k ▷ X k j) ⊎ (σ X i j ≈ I i j)
    σXᵢⱼ≈Aᵢₖ▷Xₖⱼ⊎Iᵢⱼ ⊕-sel X i j with ∃-foldr ⊕-sel (I i j) (extensions X i j)
    ... | inj₁ (k , σXᵢⱼ≈extₖ) = inj₁ (k , (trans σXᵢⱼ≈extₖ (reflexive (lookup-extensions X i j k))))
    ... | inj₂ σXᵢⱼ≈Iᵢⱼ  = inj₂ σXᵢⱼ≈Iᵢⱼ

    -- Under the following assumptions about ⊕, A▷ₘ always chooses the "best" option with respect to ⊕
    σXᵢⱼ≤Aᵢₖ▷Xₖⱼ : Selective _≈_ _⊕_ → Commutative _≈_ _⊕_ → Associative _≈_ _⊕_ → ∀ X i j l → σ X i j ≤ᵣ A i l ▷ X l j
    σXᵢⱼ≤Aᵢₖ▷Xₖⱼ ⊕-sel ⊕-comm ⊕-assoc X i j l = trans (⊕-pres-≈ (sym (reflexive (lookup-extensions X i j l))) refl) (foldrₓₛ≤xsᵢ ⊕-sel ⊕-comm ⊕-assoc (I i j) (extensions X i j) l)

    -- After an iteration, the diagonal of the RMatrix is always the identity
    σXᵢᵢ≈Iᵢᵢ : Selective _≈_ _⊕_ → Associative _≈_ _⊕_ → Commutative _≈_ _⊕_ → (∀ i s r → I i i ≤ᵣ s ▷ r) → ∀ X i → σ X i i ≈ I i i
    σXᵢᵢ≈Iᵢᵢ ⊕-sel ⊕-assoc ⊕-comm Iᵢᵢ-almost-anᵣ-⊕ X i with σXᵢⱼ≈Aᵢₖ▷Xₖⱼ⊎Iᵢⱼ ⊕-sel X i i
    ... | inj₂ σXᵢᵢ≈Iᵢᵢ = σXᵢᵢ≈Iᵢᵢ
    ... | inj₁ (k , σXᵢᵢ≈AᵢₖXₖⱼ) = ≤ᵣ-antisym ⊕-comm (foldrₑ≤e ⊕-sel ⊕-comm ⊕-assoc (I i i) (extensions X i i)) (≤ᵣ-resp-≈ refl (sym (trans σXᵢᵢ≈AᵢₖXₖⱼ refl)) (Iᵢᵢ-almost-anᵣ-⊕ i (A i k) (X k i)))

    -- After an iteration, the diagonals of any two RMatrices are equal
    σXᵢᵢ≈σYᵢᵢ : Selective _≈_ _⊕_ → Associative _≈_ _⊕_ → Commutative _≈_ _⊕_ → (∀ i s r → I i i ≤ᵣ s ▷ r) → ∀ X Y i → σ X i i ≈ σ Y i i
    σXᵢᵢ≈σYᵢᵢ ⊕-sel ⊕-assoc ⊕-comm Iᵢᵢ-almost-anᵣ-⊕ X Y i = trans (σXᵢᵢ≈Iᵢᵢ ⊕-sel ⊕-assoc ⊕-comm Iᵢᵢ-almost-anᵣ-⊕ X i) (sym (σXᵢᵢ≈Iᵢᵢ ⊕-sel ⊕-assoc ⊕-comm Iᵢᵢ-almost-anᵣ-⊕ Y i))


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





    -- Redefining some of the properties above for ease
    module UnderAssumptions (cc : ConvergenceConditions rp) where

      open ConvergenceConditions cc

      σXᵢⱼ≤Aᵢₖ▷Xₖⱼ' : ∀ X i j k → σ X i j ≤ᵣ A i k ▷ X k j
      σXᵢⱼ≤Aᵢₖ▷Xₖⱼ' = σXᵢⱼ≤Aᵢₖ▷Xₖⱼ ⊕-sel ⊕-comm ⊕-assoc

      σXᵢⱼ≈Aᵢₖ▷Xₖⱼ⊎Iᵢⱼ' : ∀ X i j → (∃ λ k → σ X i j ≈ A i k ▷ X k j) ⊎ (σ X i j ≈ I i j)
      σXᵢⱼ≈Aᵢₖ▷Xₖⱼ⊎Iᵢⱼ' = σXᵢⱼ≈Aᵢₖ▷Xₖⱼ⊎Iᵢⱼ ⊕-sel

      σXᵢᵢ≈Iᵢᵢ' : ∀ X i → σ X i i ≈ I i i
      σXᵢᵢ≈Iᵢᵢ' = σXᵢᵢ≈Iᵢᵢ ⊕-sel ⊕-assoc ⊕-comm Iᵢᵢ-almost-anᵣ-⊕

      σXᵢᵢ≈σYᵢᵢ' : ∀ X Y i → σ X i i ≈ σ Y i i
      σXᵢᵢ≈σYᵢᵢ' = σXᵢᵢ≈σYᵢᵢ ⊕-sel ⊕-assoc ⊕-comm Iᵢᵢ-almost-anᵣ-⊕

      σXᵢⱼ≈σYᵢⱼ' : ∀ X Y i j → (∀ k → (A i k ▷ X k j ≈ A i k ▷ Y k j) ⊎ ((∃ λ l → (A i l ▷ X l j) <ᵣ (A i k ▷ X k j)) × (∃ λ m → (A i m ▷ Y m j) <ᵣ (A i k ▷ Y k j)))) → σ X i j ≈ σ Y i j
      σXᵢⱼ≈σYᵢⱼ' = σXᵢⱼ≈σYᵢⱼ ⊕-sel ⊕-assoc ⊕-comm
