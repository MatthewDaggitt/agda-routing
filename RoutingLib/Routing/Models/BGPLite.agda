open import Data.Nat using (ℕ)

module RoutingLib.Routing.Models.BGPLite (n : ℕ) where

  open import Data.Nat.Properties
    using (_<?_; <-cmp; <-trans; <-irrefl; <-asym; m+n≮n; m≤m+n; <⇒≱; ≤-refl; ≤-trans)
  open import Data.List using (List)
  open import Data.Bool as 𝔹 using (Bool; _∧_; _∨_)
  open import Data.Product using (_,_; _×_; proj₁; proj₂)
  open import Data.Fin using (Fin; fromℕ≤)
  open import Data.Sum using (_⊎_; [_,_]′; inj₁; inj₂)
  open import Relation.Unary using (Pred)
  open import Relation.Nullary using (¬_; yes; no)
  open import Relation.Nullary.Negation using (contradiction)
  open import Relation.Binary
  open import Relation.Binary.PropositionalEquality
    using (_≡_; refl; sym; trans; subst; cong; cong₂; inspect; [_])
  open import Relation.Binary.Lattice using (Minimum; Maximum)
  open import Level using () renaming (zero to ℓ₀; suc to lsuc)

  open import RoutingLib.Data.Nat.Properties using (n≢1+n)
  open import RoutingLib.Data.Graph.SimplePath2
    using (SimplePath; invalid; valid)
    renaming (_≈_ to _≈ᵢₚ_)
  open import RoutingLib.Data.Graph.SimplePath2.NonEmpty
    using (SimplePathⁿᵗ; []; _∷_∣_∣_; _∷_; length; _⇿_; _∉_; _∈_; _<ₗₑₓ_; <ₗₑₓ-cmp; <ₗₑₓ-trans; <ₗₑₓ-resp-≈; <ₗₑₓ-asym; <ₗₑₓ-irrefl; <ₗₑₓ-minimum; <ₗₑₓ-respˡ-≈; <ₗₑₓ-respʳ-≈)
    renaming (_≈_ to _≈ₚ_)
  open import RoutingLib.Data.Graph.SimplePath2.NonEmpty.Properties
    using (_⇿?_; ⇿-resp-≈; ∉-resp-≈; length-cong; p≉i∷p)
    renaming (_∈?_ to _∈ₚ?_; _∉?_ to _∉ₚ?_; ≈-refl to ≈ₚ-refl; ≈-trans to ≈ₚ-trans; ≈-sym to ≈ₚ-sym; _≟_ to _≟ₚ_)
  import RoutingLib.Relation.Binary.NaturalOrder.Right as RightNaturalOrder
  open import RoutingLib.Routing.BellmanFord.PathVector.SufficientConditions
  open import RoutingLib.Routing.Definitions
  import RoutingLib.Algebra.Selectivity.NaturalChoice as NaturalChoice

  
  open import RoutingLib.Routing.Models.BGPLite.Route n
  open import RoutingLib.Routing.Models.BGPLite.Route.Properties n
  open import RoutingLib.Routing.Models.BGPLite.Policy n
  open import RoutingLib.Routing.Models.BGPLite.Communities

  open import Algebra.FunctionProperties _≈ᵣ_
  
  ------------
  -- Syntax --
  ------------

  data Step : Set₁ where
    step : Node → Node → Policy → Step

  0# : Route
  0# = invalid
 
  1# : Route
  1# = route 0 ∅ []
  
  infix 5 _⊕_
  _⊕_ : Op₂ Route
  _⊕_ = NaturalChoice._•_ ≤ᵣ-total

  ⊕-cong : Congruent₂ _⊕_
  ⊕-cong = NaturalChoice.cong ≤ᵣ-total _≈ᵣ_ ≈ᵣ-refl ≈ᵣ-sym ≤ᵣ-antisym ≤ᵣ-resp-≈ᵣ

  infix 5 _▷_
  _▷_ : Step → Route → Route
  _              ▷ invalid       = invalid
  (step i j pol) ▷ (route x c p) with (i , j) ⇿? p | i ∉ₚ? p
  ... | no  _   | _       = invalid
  ... | yes _   | no  _   = invalid
  ... | yes i⇿p | yes i∉p with apply pol (route x c p)
  ...   | invalid          = invalid
  ...   | (route nl ncs _) = route nl ncs ((i , j) ∷ p ∣ i⇿p ∣ i∉p)
  
  ▷-cong : ∀ f {r s} → r ≈ᵣ s → f ▷ r ≈ᵣ f ▷ s
  ▷-cong (step i j pol) {_}            {_}            invalidEq = invalidEq
  ▷-cong (step i j pol) {r@(route l cs p)} {s@(route k ds q)} r≈s@(routeEq l≡k cs≈ds p≈q)
    with (i , j) ⇿? p | (i , j) ⇿? q
  ... | no _    | no _    = invalidEq 
  ... | no ¬e⇿p | yes e⇿q = contradiction (⇿-resp-≈ (≈ₚ-sym p≈q) e⇿q) ¬e⇿p
  ... | yes e⇿p | no ¬e⇿q = contradiction (⇿-resp-≈ p≈q e⇿p) ¬e⇿q
  ... | yes _   | yes _ with i ∉ₚ? p | i ∉ₚ? q
  ...   | no _    | no  _   = invalidEq 
  ...   | no  i∈p | yes i∉q = contradiction (∉-resp-≈ (≈ₚ-sym p≈q) i∉q) i∈p
  ...   | yes i∉p | no  i∈q = contradiction (∉-resp-≈ p≈q i∉p) i∈q
  ...   | yes _  | yes _  with
    apply pol r | apply pol s | inspect (apply pol) r | inspect (apply pol) s
  ...     | invalid     | invalid     | _        | _ = invalidEq
  ...     | invalid     | route _ _ _ | [ pᵣ≡i ] | [ pₛ≡r ] =
    contradiction (apply-trans pol r≈s pᵣ≡i pₛ≡r) λ()
  ...     | route _ _ _ | invalid     | [ pᵣ≡r ] | [ pₛ≡i ] =
    contradiction (apply-trans pol r≈s pᵣ≡r pₛ≡i) λ()
  ...     | route _ _ _ | route _ _ _ | [ pᵣ≡r ] | [ pₛ≡r ] with apply-trans pol r≈s pᵣ≡r pₛ≡r
  ...       | routeEq leq ceq _ = routeEq leq ceq (refl ∷ p≈q)

  algebra : RoutingAlgebra _ _ _
  algebra = record
    { Step   = Step
    ; Route  = Route
    ; _⊕_    = _⊕_
    ; _▷_    = _▷_
    ; 0#     = invalid
    ; 1#     = 1#
    ; _≈_    = _≈ᵣ_
    ; ≈-isDecEquivalence = ≈ᵣ-isDecEquivalence
    ; ⊕-cong = ⊕-cong
    ; ▷-cong = ▷-cong
    }
    
  ---------------------
  -- Choice operator --
  ---------------------
  
  ⊕-sel : Selective _⊕_
  ⊕-sel = NaturalChoice.sel ≤ᵣ-total _≈ᵣ_ ≈ᵣ-refl
  
  ⊕-assoc : Associative _⊕_
  ⊕-assoc = NaturalChoice.assoc ≤ᵣ-total _≈ᵣ_ ≈ᵣ-refl ≤ᵣ-antisym ≤ᵣ-trans
  
  ⊕-comm : Commutative _⊕_
  ⊕-comm = NaturalChoice.comm ≤ᵣ-total _≈ᵣ_ ≈ᵣ-refl ≤ᵣ-antisym

  ⊕-identityʳ  : RightIdentity invalid _⊕_
  ⊕-identityʳ = NaturalChoice.idᵣ ≤ᵣ-total _≈ᵣ_ ≈ᵣ-refl ≤ᵣ-antisym ≤ᵣ-maximum

  ⊕-zeroʳ : RightZero 1# _⊕_
  ⊕-zeroʳ = NaturalChoice.anᵣ ≤ᵣ-total _≈ᵣ_ ≈ᵣ-refl ≤ᵣ-antisym ≤ᵣ-minimum

  -----------
  -- Steps --
  -----------
  
  ▷-zero : ∀ f → f ▷ invalid ≈ᵣ invalid
  ▷-zero (step _ _ _) = invalidEq

  open RightNaturalOrder _≈ᵣ_ _⊕_ using () renaming (_<_ to _<₊_)
  
  ⊕-strictlyAbsorbs-▷ : ∀ f {x} → x ≉ᵣ invalid → x <₊ f ▷ x
  ⊕-strictlyAbsorbs-▷ f              {invalid}      x≉ᵣinv = contradiction invalidEq x≉ᵣinv
  ⊕-strictlyAbsorbs-▷ (step i j pol) {route l cs p} x≉ᵣinv with (i , j) ⇿? p | i ∉ₚ? p
  ... | no  _   | _       = ≈ᵣ-refl , x≉ᵣinv
  ... | yes _   | no  _   = ≈ᵣ-refl , x≉ᵣinv
  ... | yes i⇿p | yes i∉p with apply pol (route l cs p) | inspect (apply pol) (route l cs p)
  ...   | invalid      | _         = ≈ᵣ-refl , x≉ᵣinv
  ...   | route k ds _ | [ app≡s ] with ≤ᵣ-total (route k ds ((i , j) ∷ p ∣ i⇿p ∣ i∉p)) (route l cs p)
  ...     | inj₂ _ = ≈ᵣ-refl , λ {(routeEq _ _ p≈i∷p) → p≉i∷p p≈i∷p}
  ...     | inj₁ (level<  k<l)           = contradiction (apply-levelIncr pol (≈ᵣ-reflexive app≡s)) (<⇒≱ k<l)
  ...     | inj₁ (length< _ |i∷p|<|p|)   = contradiction |i∷p|<|p| (m+n≮n 1 _)
  ...     | inj₁ (plex<   _ |i∷p|≡|p| _) = contradiction (sym |i∷p|≡|p|) (n≢1+n _)
  ...     | inj₁ (comm≤   _ i∷p≈p     _) = contradiction (≈ₚ-sym i∷p≈p) p≉i∷p

  --------------------------------
  -- A specific routing problem --
  --------------------------------

  postulate topology : Fin n → Fin n → Policy
  
  A : Fin n → Fin n → Step
  A i j = step i j (topology i j)
  
  problem : RoutingProblem algebra n
  problem = record
    { A = A
    }

  ------------------------------
  -- Path projection function --
  ------------------------------

  path : Route → SimplePath n
  path invalid       = invalid
  path (route _ _ p) = valid p

  path-cong : ∀ {r s} → r ≈ᵣ s → path r ≈ᵢₚ path s
  path-cong invalidEq         = invalid
  path-cong (routeEq _ _ p≈q) = valid p≈q
  
  r≈1⇒path[r]≈[] : ∀ {r} → r ≈ᵣ 1# → path r ≈ᵢₚ valid []
  r≈1⇒path[r]≈[] (routeEq _ _ []) = valid []

  r≈0⇒path[r]≈∅ : ∀ {r} → r ≈ᵣ invalid → path r ≈ᵢₚ invalid
  r≈0⇒path[r]≈∅ invalidEq = invalid
  
  path[r]≈∅⇒r≈0 : ∀ {r} → path r ≈ᵢₚ invalid → r ≈ᵣ invalid
  path[r]≈∅⇒r≈0 {invalid}      invalid = invalidEq
  path[r]≈∅⇒r≈0 {route l cs p} ()
  
  path-reject : ∀ {i j r q} → path r ≈ᵢₚ valid q → ¬ (i , j) ⇿ q ⊎ i ∈ q → A i j ▷ r ≈ᵣ invalid
  path-reject {i} {j} {invalid}      pᵣ≈p        inv = invalidEq
  path-reject {i} {j} {route l cs p} (valid p≈q) inv with (i , j) ⇿? p | i ∉ₚ? p
  ... | no  _    | _       = invalidEq
  ... | yes _    | no  _   = invalidEq
  ... | yes ij⇿p | yes i∉p with inv
  ...   | inj₁ ¬ij⇿p = contradiction (⇿-resp-≈ p≈q ij⇿p) ¬ij⇿p
  ...   | inj₂ i∈p   = contradiction (∉-resp-≈ p≈q i∉p) i∈p
  
  path-accept : ∀ {i j r q} → path r ≈ᵢₚ valid q → A i j ▷ r ≉ᵣ invalid →
                ∀ ij⇿q i∉q → path (A i j ▷ r) ≈ᵢₚ valid ((i , j) ∷ q ∣ ij⇿q ∣ i∉q)
  path-accept {i} {j} {invalid}      pᵣ≈q        Aᵢⱼ▷r≉0 ij⇿q i∉q = contradiction invalidEq Aᵢⱼ▷r≉0
  path-accept {i} {j} {route l cs p} (valid p≈q) Aᵢⱼ▷r≉0 ij⇿q i∉q with (i , j) ⇿? p | i ∉ₚ? p
  ... | no ¬ij⇿p | _       = contradiction (⇿-resp-≈ (≈ₚ-sym p≈q) ij⇿q) ¬ij⇿p
  ... | yes _    | no  i∈p = contradiction (∉-resp-≈ (≈ₚ-sym p≈q) i∉q) i∈p
  ... | yes _    | yes _   with apply (topology i j) (route l cs p)
  ...   | invalid     = contradiction invalidEq Aᵢⱼ▷r≉0
  ...   | route _ _ _ = valid (refl ∷ p≈q)
  
  conditions : PathSufficientConditions problem
  conditions = record
    { ⊕-assoc             = ⊕-assoc
    ; ⊕-sel               = ⊕-sel
    ; ⊕-comm              = ⊕-comm
    ; ⊕-strictlyAbsorbs-▷ = ⊕-strictlyAbsorbs-▷
    ; ⊕-zeroʳ             = ⊕-zeroʳ
    ; ▷-zero              = ▷-zero
    ; ⊕-identityʳ         = ⊕-identityʳ
    
    ; path           = path
    ; path-cong      = path-cong
    ; r≈1⇒path[r]≈[] = r≈1⇒path[r]≈[]
    ; r≈0⇒path[r]≈∅  = r≈0⇒path[r]≈∅
    ; path[r]≈∅⇒r≈0  = path[r]≈∅⇒r≈0
    ; path-reject    = path-reject
    ; path-accept    = path-accept
    }
