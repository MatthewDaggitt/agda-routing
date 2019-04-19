
open import RoutingLib.Routing.Algebra

module RoutingLib.Routing.Algebra.Construct.AddPathsProperties
  {a b ℓ} (A : RawRoutingAlgebra a b ℓ)
          (A-IsRoutingAlgebra  : IsRoutingAlgebra A) where

open import Algebra.Construct.NaturalChoice.Min
open import Algebra.FunctionProperties
open import Data.Nat using (zero; suc)
open import Data.Fin using (Fin; toℕ)
open import Data.Maybe using (Maybe; just)
open import Data.Maybe.Relation.Unary.Any using (just)
open import Data.Maybe.Relation.Unary.All using (just)
open import Data.Product
open import Data.Product.Relation.Pointwise.NonDependent as Pointwise using (Pointwise)
open import Data.Sum as Sum using (_⊎_; inj₁; inj₂)
open import Function using (_∘_)
open import Level using (Lift; lift; _⊔_)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
import Relation.Binary.EqReasoning as EqReasoning
open import Relation.Binary.Construct.Add.Point.Equality as PointedEq
  renaming (_≈∙_ to PointedEq)
  using (∙≈∙; [_]; [≈]-injective; ≈∙-refl; ≈∙-sym; ≈∙-trans)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Nullary.Construct.Add.Point renaming (∙ to invalid; [_] to valid)

open import RoutingLib.Relation.Binary.Construct.NaturalOrder.Right using (antisym) 
open import RoutingLib.Algebra.Construct.Add.Identity as AddIdentity
  renaming (_⊕∙_ to AddIdentity) using (⊕∙-comm)
open import RoutingLib.Algebra.Construct.Lexicographic as Lex
  using (Lex; Lex₂)
open import RoutingLib.Algebra.Construct.Lexicographic.Magma as OpLexProperties′
open import RoutingLib.Data.Path.Uncertified.Choice using (_⊓ₗₑₓ_)  --- Minₗₑₓ._⊓_
open import RoutingLib.Data.Path.Uncertified.Properties
open import RoutingLib.Data.Path.UncertifiedI using (Pathᵛ; Path; _∉ᵥₚ_; _∈ᵥₚ_; _⇿ᵥ_; _∈ₚ_; _∉ₚ_;_⇿_;_∷_ ) 

open import RoutingLib.Routing.Algebra.Construct.AddPaths A
     using (AddPaths; isRoutingAlgebra; isPathAlgebra; ⊕⁺-idem; ⊕⁺invalidᵣ; ⊕⁺invalidₗ; ≤₊⁺⇒≤⁺) 


open RawRoutingAlgebra A
open IsRoutingAlgebra A-IsRoutingAlgebra

no-∞-sum : ∀ {x y} → x ≉ ∞# → y ≉ ∞# → (x ⊕ y) ≉ ∞#
no-∞-sum {x} {y} x≉∞ y≉∞  with ⊕-sel x y
... | inj₁ x⊕y≈x = λ x⊕y≈∞ → contradiction (≈-trans (≈-sym x⊕y≈x) x⊕y≈∞) x≉∞
... | inj₂ x⊕y≈y = λ x⊕y≈∞ → contradiction (≈-trans (≈-sym x⊕y≈y) x⊕y≈∞) y≉∞



Aᵖ : RawRoutingAlgebra a b (a ⊔ ℓ)
Aᵖ = AddPaths

open RawRoutingAlgebra Aᵖ using () renaming
     (Route              to Route⁺ ; 
      Step               to Step⁺  ;
      _≈_                to _≈⁺_   ;
      _⊕_                to _⊕⁺_   ; 
      _▷_                to _▷⁺_   ;
      0#                 to 0#⁺    ;
      ∞#                 to ∞#⁺    ; 
      f∞                 to f∞⁺    ;
      ≈-isDecEquivalence to ≈⁺-isDecEquivalence ;
      ⊕-cong             to ⊕⁺-cong    ; 
      ▷-cong             to ▷⁺-cong    ;
      f∞-reject          to f∞⁺-reject ;
      ≤₊-respˡ-≈          to  ≤₊⁺-respˡ-≈⁺;
      ≤₊-respʳ-≈          to  ≤₊⁺-respʳ-≈⁺;
      _≤₊_               to _≤₊⁺_;
      S             to S⁺
     )

Aᵖ-IsRoutingAlgebra : IsRoutingAlgebra Aᵖ
Aᵖ-IsRoutingAlgebra = isRoutingAlgebra A-IsRoutingAlgebra   
     where open IsRoutingAlgebra A-IsRoutingAlgebra

open IsRoutingAlgebra Aᵖ-IsRoutingAlgebra  renaming
     (⊕-sel        to ⊕⁺-sel        ;
      ⊕-comm       to ⊕⁺-comm       ;
      ⊕-assoc      to ⊕⁺-assoc      ;
      ⊕-zeroʳ      to ⊕⁺-zeroʳ       ;
      ⊕-identityʳ  to ⊕⁺-identityʳ   ;
      ▷-fixedPoint to ▷⁺-fixedPoint  
      )

open IsDecEquivalence ≈⁺-isDecEquivalence renaming
     (_≟_  to _≟⁺_    ;
      isEquivalence to ≈⁺-isEquivalence
     )

open IsEquivalence ≈⁺-isEquivalence renaming
     (refl  to ≈⁺-refl ;
      sym   to ≈⁺-sym ;
      trans to ≈⁺-trans
     )

Aᵖ-IsPathAlgebra : IsPathAlgebra Aᵖ
Aᵖ-IsPathAlgebra = isPathAlgebra

open IsPathAlgebra Aᵖ-IsPathAlgebra 
{-   using 
     (path ;          
      path-cong ;
      r≈0⇒path[r]≈[] ;
      r≈∞⇒path[r]≈∅ ;
      path[r]≈∅⇒r≈∞ ;
      path-reject    ;
      path-accept    
    )
-}


open PathDistributivity Aᵖ-IsPathAlgebra

cong-path-distrib : ∀ a b c d  → a ≈⁺ c → b ≈⁺ d → ∀ k →
                    IsLevel k PathDistributiveIn[ a , b ] →
                    IsLevel k PathDistributiveIn[ c , d ]

cong-path-distrib a b c d a≈⁺c b≈⁺d zero dis[a,b] {n} {i} {j} f {x} {y} c≤₊x x≤₊d c≤₊y y≤₊d i∉ₚpathx i∉ₚpathy  ij⇿pathx ij⇿pathy =  cnc
  where
  cnc : f ▷⁺ (x ⊕⁺ y) ≈⁺  (f ▷⁺ x) ⊕⁺ (f ▷⁺ y)
  cnc =  dis[a,b] {n} {i} {j} f {x} {y}
      (≤₊⁺-respˡ-≈⁺ {x} (≈⁺-sym a≈⁺c) c≤₊x) 
      (≤₊⁺-respʳ-≈⁺ (≈⁺-sym b≈⁺d) x≤₊d)
      (≤₊⁺-respˡ-≈⁺ {y}  (≈⁺-sym a≈⁺c) c≤₊y) 
      (≤₊⁺-respʳ-≈⁺ (≈⁺-sym b≈⁺d) y≤₊d) 
      i∉ₚpathx  i∉ₚpathy  ij⇿pathx ij⇿pathy  
  
cong-path-distrib a b c d a≈⁺c b≈⁺d (suc k) dis[a,b] {n} {i} {j} f {x} {y} c≤₊x x≤₊d c≤₊y y≤₊d i∉ₚpathx i∉ₚpathy  =  cnc
  where
  cnc : IsLevel k PathDistributiveIn[ f ▷⁺ (x ⊕⁺ y) ,  (f ▷⁺ x) ⊕⁺ (f ▷⁺ y)  ]
  cnc =  dis[a,b] {n} {i} {j} f {x} {y}
      (≤₊⁺-respˡ-≈⁺ {x} (≈⁺-sym a≈⁺c) c≤₊x) 
      (≤₊⁺-respʳ-≈⁺ (≈⁺-sym b≈⁺d) x≤₊d) 
      (≤₊⁺-respˡ-≈⁺ {y}  (≈⁺-sym a≈⁺c) c≤₊y) 
      (≤₊⁺-respʳ-≈⁺ (≈⁺-sym b≈⁺d) y≤₊d) 
      i∉ₚpathx  i∉ₚpathy


≤₊⁺-antisym : Antisymmetric _≈⁺_ _≤₊⁺_
≤₊⁺-antisym = antisym _ _ ≈⁺-isEquivalence ⊕⁺-comm       

∉ₚto∉̂ᴱ : ∀ {n x p} {i : Fin n} → toℕ i ∉ₚ path (valid (x , p)) → toℕ i ∉ᵥₚ p 
∉ₚto∉̂ᴱ i∉ₚ = i∉ₚ ∘ just

∈ᵥₚ=>∈ₚ : ∀ {n p} {i : Fin n} → toℕ i ∈ᵥₚ p → toℕ i ∈ₚ (valid p)
∈ᵥₚ=>∈ₚ {n} {p} {i} i∈ᵥₚp = just i∈ᵥₚp


pres-distrib : ∀ {k ⊤ ⊥} p q → Level_DistributiveIn[_,_]Alt A k ⊥ ⊤ →
               IsLevel_PathDistributiveIn[_,_]Alt k (valid (⊥ , p)) (valid (⊤ , q))
pres-distrib {zero}  {⊤} {⊥} p q (lift ⊥≈⊤) = Level.lift [ ⊥≈⊤ , {!!} ]
pres-distrib {suc k} {⊤} {⊥} p q distrib f {invalid} {invalid} ⊥≤x x≤⊤ ⊥≤y y≤⊤ i∉px i∉py ij⇿px ij⇿py = res
  where
  res : IsLevel k PathDistributiveIn[ invalid , invalid ]Alt
  res = {!!}
pres-distrib {suc k} {⊤} {⊥} p q distrib f {invalid} {valid y}       ⊥≤x x≤⊤ ⊥≤y y≤⊤ i∉px i∉py ij⇿px ij⇿py = res
  where
  res : IsLevel k PathDistributiveIn[ f ▷⁺ (valid y) , f ▷⁺ (valid y) ]Alt
  res = {!!}
pres-distrib {suc k} {⊤} {⊥} p q distri f {valid x}       {invalid} ⊥≤x x≤⊤ ⊥≤y y≤⊤ i∉px i∉py ij⇿px ij⇿py = res
  where
  res : IsLevel k PathDistributiveIn[ f ▷⁺ valid x , (f ▷⁺ valid x) ⊕⁺ invalid ]Alt
  res = {!!}
pres-distrib {suc k} {⊤} {⊥} p q distrib f {valid (x , r)} {valid (y , s)} ⊥≤x x≤⊤ ⊥≤y y≤⊤ i∉px i∉py ij⇿px ij⇿py
  = {!distrib ? ? ? ? ?!}
  where
  test : Level_DistributiveIn[_,_]Alt A k (f ▷ x ⊕ y) ((f ▷ x) ⊕ (f ▷ y))
  test = distrib f {!≤₊⁺⇒≤⁺ ?!} {!!} {!!} {!!} 
