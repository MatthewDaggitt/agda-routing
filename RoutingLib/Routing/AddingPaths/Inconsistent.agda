open import Level using (_⊔_)
open import Data.Nat using (ℕ; suc) renaming (_≤_ to _≤ℕ_)
open import Relation.Nullary using (¬_; yes; no)
open import Data.Product using (_×_; _,_)
open import Data.Fin using (Fin)
open import Data.Fin.Properties using () renaming (_≟_ to _≟ᶠ_)
open import Data.Maybe using (just; nothing)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality using (_≡_; subst) renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans)
open import Algebra.FunctionProperties using (Op₂)

open import RoutingLib.Algebra.FunctionProperties using (_Preserves_; _Preservesₗ_; Selective)
open import RoutingLib.Routing.Definitions
open import RoutingLib.Data.Graph using (Graph; _ᵉ∈ᵍ?_)
open import RoutingLib.Data.Graph.EPath
open import RoutingLib.Data.Graph.EPath.Properties
open import RoutingLib.Relation.Binary.RespectedBy using (_RespectedBy_; Respects₂⇨RespectedBy)


module RoutingLib.Routing.AddingPaths.Inconsistent
  {a b ℓ} (ra : RoutingAlgebra a b ℓ) 
  (⊕-sel : Selective (RoutingAlgebra._≈_ ra) (RoutingAlgebra._⊕_ ra))
  (one : (RoutingAlgebra.Route ra))
  {n : ℕ}
  (G : Graph (RoutingAlgebra.Step ra) n)
  where
  
  -----------
  -- Setup --
  -----------

  open RoutingAlgebra ra

  open import RoutingLib.Algebra.Selectivity.Properties _≈_ _⊕_ ⊕-sel using (selection; SelCase)
  open import RoutingLib.Algebra.Selectivity.Properties _≈_ _⊕_ ⊕-sel using (sel₁; sel₂; sel≈) public
  
  select : ∀ x y → SelCase x y
  select = selection sym trans _≟_


  --------------------------------
  -- Consistent routing algebra --
  --------------------------------
    
  -- Routes are formed by the product R × EPath along with a zero added (the null path)
 
  data IRoute : Set (a ⊔ b ⊔ ℓ) where
    inull  : IRoute
    iroute : Route → EPath n → IRoute


  -- Steps
  
  open import RoutingLib.Algebra.AddingElements (Fin n × Fin n × Step) using () renaming (Aₑ to IStep; val to iedge; e to inone) public


  -- Equality

  infix 4 _≈ⁱ_ _≉ⁱ_

  data _≈ⁱ_ : Rel IRoute (a ⊔ b ⊔ ℓ) where
    inullEq  : inull ≈ⁱ inull
    irouteEq : ∀ {x y p q} → x ≈ y → p ≈ₚ q → iroute x p ≈ⁱ iroute y q

  _≉ⁱ_ : Rel IRoute (a ⊔ b ⊔ ℓ)
  x ≉ⁱ y = ¬ (x ≈ⁱ y) 



  -- Choice operator

  open import RoutingLib.Relation.Binary.PreorderLex (_≤ₗ_ {n = n}) _≤ₚ_ 
    using (×-isDecTotalOrder) 
    renaming (×-Lex to _≤ₗₚ_) 
    public

  open IsDecTotalOrder (×-isDecTotalOrder ≤ₗ-isDecTotalPreorder ≤ₚ-isDecTotalOrder) using () renaming (
      refl to ≤ₗₚ-refl;
      trans to ≤ₗₚ-trans;
      antisym to ≤ₗₚ-antisym;
      total to ≤ₗₚ-total; 
      _≤?_ to _≤ₗₚ?_;
      ≤-resp-≈ to ≤ₗₚ-resp₂-≈
    ) public

  ≤ₗₚ-resp-≈ₚ : _≤ₗₚ_ RespectedBy _≈ₚ_
  ≤ₗₚ-resp-≈ₚ = Respects₂⇨RespectedBy ≤ₗₚ-resp₂-≈

  infix 7 _⊕ⁱ_

  _⊕ⁱ_ : Op₂ IRoute
  inull ⊕ⁱ r     = r
  r     ⊕ⁱ inull = r
  (iroute x p) ⊕ⁱ (iroute y q) with select x y
  ... | sel₁ _ _ = iroute x p
  ... | sel₂ _ _ = iroute y q
  ... | sel≈ _ _ with p ≤ₗₚ? q
  ...   | yes _ = iroute x p
  ...   | no  _ = iroute y q




  -- Extension operator
  
  infix 6 _▷ⁱ_

  _▷ⁱ_ : IStep → IRoute → IRoute
  inone             ▷ⁱ _                          = inull
  _                 ▷ⁱ inull                      = inull
  iedge (i , j , e) ▷ⁱ (iroute x p) with j ≟ᶠ source p | i ∉? p
  ... | no _       | _       = inull
  ... | _          | no  _   = inull
  ... | yes j≡s[p] | yes i∉p = iroute (e ▷ x) (i ∷ p ∣ i∉p)
  

  -- Equality properties

  abstract

    -- equality is a decidable equivalence

    ≈ⁱ-refl : Reflexive _≈ⁱ_
    ≈ⁱ-refl {inull} = inullEq
    ≈ⁱ-refl {iroute _ _} = irouteEq refl ≈ₚ-refl

    ≈ⁱ-reflexive : _≡_ ⇒ _≈ⁱ_
    ≈ⁱ-reflexive ≡-refl = ≈ⁱ-refl

    ≈ⁱ-sym : Symmetric _≈ⁱ_
    ≈ⁱ-sym inullEq            = inullEq
    ≈ⁱ-sym (irouteEq x≈y p≈q) = irouteEq (sym x≈y) (≈ₚ-sym p≈q)

    ≈ⁱ-trans : Transitive _≈ⁱ_
    ≈ⁱ-trans inullEq inullEq = inullEq
    ≈ⁱ-trans (irouteEq x≈y p≈q) (irouteEq y≈z q≈r) = irouteEq (trans x≈y y≈z) (≈ₚ-trans p≈q q≈r)

    _≟ⁱ_ : Decidable _≈ⁱ_
    inull ≟ⁱ inull = yes inullEq
    inull ≟ⁱ (iroute _ _) = no λ()
    (iroute _ _) ≟ⁱ inull = no λ()
    (iroute x p) ≟ⁱ (iroute y q) with x ≟ y | p ≟ₚ q
    ... | no  x≉y | _       = no λ{(irouteEq x≈y _) → x≉y x≈y}
    ... | _       | no  p≉q = no λ{(irouteEq _ p≈q) → p≉q p≈q}
    ... | yes x≈y | yes p≈q = yes (irouteEq x≈y p≈q)

    ≈ⁱ-isEquivalence : IsEquivalence _≈ⁱ_
    ≈ⁱ-isEquivalence = record { 
        refl = ≈ⁱ-refl ; 
        sym = ≈ⁱ-sym ; 
        trans = ≈ⁱ-trans 
      }

    ≈ⁱ-isDecEquivalence : IsDecEquivalence _≈ⁱ_
    ≈ⁱ-isDecEquivalence = record { 
        isEquivalence = ≈ⁱ-isEquivalence ; 
        _≟_ = _≟ⁱ_ 
      }
    
  ≈ⁱ-setoid : Setoid (a ⊔ b ⊔ ℓ) (a ⊔ b ⊔ ℓ)
  ≈ⁱ-setoid = record {
      _≈_ = _≈ⁱ_; 
      isEquivalence = ≈ⁱ-isEquivalence
    }

  abstract

    ⊕ⁱ-pres-≈ⁱ : _⊕ⁱ_ Preserves _≈ⁱ_
    ⊕ⁱ-pres-≈ⁱ inullEq inullEq = inullEq
    ⊕ⁱ-pres-≈ⁱ inullEq (irouteEq y≈z r≈s) = irouteEq y≈z r≈s
    ⊕ⁱ-pres-≈ⁱ (irouteEq w≈x p≈q) inullEq = irouteEq w≈x p≈q
    ⊕ⁱ-pres-≈ⁱ {iroute w p} {iroute x q} {iroute y r} {iroute z s} (irouteEq w≈x p≈q) (irouteEq y≈z r≈s) with select w y | select x z
    ... | sel₁ _     _     | sel₁ _     _     = irouteEq w≈x p≈q
    ... | sel₁ _     w⊕y≉y | sel₂ _     x⊕z≈z = contradiction (trans (trans (⊕-pres-≈ w≈x y≈z) x⊕z≈z) (sym y≈z)) w⊕y≉y
    ... | sel₁ _     w⊕y≉y | sel≈ _     x⊕z≈z = contradiction (trans (trans (⊕-pres-≈ w≈x y≈z) x⊕z≈z) (sym y≈z)) w⊕y≉y
    ... | sel₂ w⊕y≉w _     | sel₁ x⊕z≈x _     = contradiction (trans (trans (⊕-pres-≈ w≈x y≈z) x⊕z≈x) (sym w≈x)) w⊕y≉w
    ... | sel₂ _     _     | sel₂ _     _     = irouteEq y≈z r≈s
    ... | sel₂ w⊕y≉w _     | sel≈ x⊕z≈x _     = contradiction (trans (trans (⊕-pres-≈ w≈x y≈z) x⊕z≈x) (sym w≈x)) w⊕y≉w
    ... | sel≈ _     w⊕y≈y | sel₁ _     x⊕z≉z = contradiction (trans (trans (sym (⊕-pres-≈ w≈x y≈z)) w⊕y≈y) y≈z) x⊕z≉z
    ... | sel≈ w⊕y≈w _     | sel₂ x⊕z≉x _     = contradiction (trans (trans (sym (⊕-pres-≈ w≈x y≈z)) w⊕y≈w) w≈x) x⊕z≉x
    ... | sel≈ _     _     | sel≈ _     _     with p ≤ₗₚ? r | q ≤ₗₚ? s
    ...   | yes _   | yes _   = irouteEq w≈x p≈q
    ...   | yes p≤r | no  q≰s = contradiction (≤ₗₚ-resp-≈ₚ p≈q r≈s p≤r) q≰s
    ...   | no  p≰r | yes q≤s = contradiction (≤ₗₚ-resp-≈ₚ (≈ₚ-sym p≈q) (≈ₚ-sym r≈s) q≤s) p≰r
    ...   | no  _   | no  _   = irouteEq y≈z r≈s

    ▷ⁱ-pres-≈ⁱ : _▷ⁱ_ Preservesₗ _≈ⁱ_
    ▷ⁱ-pres-≈ⁱ {b = inone}             _       = inullEq
    ▷ⁱ-pres-≈ⁱ {b = iedge (_ , _ , _)} inullEq = inullEq
    ▷ⁱ-pres-≈ⁱ {b = iedge (i , j , v)} {iroute x p} {iroute y q} (irouteEq x≈y p≈q) with j ≟ᶠ source p | j ≟ᶠ source q | i ∉? p | i ∉? q
    ... | no  _    | no  _    | _       | _       = inullEq
    ... | no  j≢p₀ | yes j≡q₀ | _       | _       = contradiction (≡-trans j≡q₀ (p≈q⇨p₀≡q₀ (≈ₚ-sym p≈q))) j≢p₀
    ... | yes j≡p₀ | no  j≢q₀ | _       | _       = contradiction (≡-trans j≡p₀ (p≈q⇨p₀≡q₀ p≈q)) j≢q₀
    ... | yes _    | yes _    | no  _   | no  _   = inullEq
    ... | yes _    | yes _    | no  i∈p | yes i∉q = contradiction (∉-resp-≈ₚ (≈ₚ-sym p≈q) i∉q) i∈p
    ... | yes _    | yes _    | yes i∉p | no  i∈q = contradiction (∉-resp-≈ₚ p≈q i∉p) i∈q
    ... | yes _    | yes _    | yes _   | yes _   = irouteEq (▷-pres-≈ v x≈y) (≡-refl ∷ p≈q)

  -- A routing algebra can now be formed

  ira : RoutingAlgebra _ _ _
  ira = record {
      Step = IStep;
      Route = IRoute;

      _⊕_ = _⊕ⁱ_;
      _▷_ = _▷ⁱ_;

      _≈_ = _≈ⁱ_;
      ≈-isDecEquivalence = ≈ⁱ-isDecEquivalence;
      ▷-pres-≈ = ▷ⁱ-pres-≈ⁱ;
      ⊕-pres-≈ = ⊕ⁱ-pres-≈ⁱ
    }


  ---------------------
  -- Routing problem --
  ---------------------

  Aⁱ : Fin n → Fin n → IStep
  Aⁱ i j with G i j
  ... | nothing = inone
  ... | just v  = iedge (i , j , v)

  Iⁱ : Fin n → Fin n → IRoute
  Iⁱ i j with j ≟ᶠ i
  ... | no  _ = inull
  ... | yes _ = iroute one [ i ]

  irp : RoutingProblem _ _ _ n
  irp = record {
       ra = ira;
       A = Aⁱ;
       I = Iⁱ
    }
