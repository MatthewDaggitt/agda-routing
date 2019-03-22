
open import RoutingLib.Routing.Algebra

module RoutingLib.Routing.Algebra.Construct.AddPathsProperties
  {a b ℓ} (A : RawRoutingAlgebra a b ℓ)
          (A-IsRoutingAlgebra  : IsRoutingAlgebra A) where

open import Algebra.FunctionProperties
open import Data.Nat using (zero; suc)
open import Data.Fin using (Fin; toℕ)
open import Data.Maybe using (Maybe; just)
--open import Data.Product using (_×_; _,_)
open import Data.Product.Relation.Pointwise.NonDependent as Pointwise using (Pointwise)
open import Data.Sum as Sum using (_⊎_; inj₁; inj₂)
--open import Function using (_∘_)
open import Relation.Binary
open import Data.Product
open import Relation.Binary.PropositionalEquality
import Relation.Binary.EqReasoning as EqReasoning
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Negation using (contradiction)

open import RoutingLib.Relation.Binary.Construct.NaturalOrder.Right using (antisym) 
open import RoutingLib.Algebra.Construct.Add.Identity as AddIdentity
  renaming (_⊕∙_ to AddIdentity) using (⊕∙-comm)
open import RoutingLib.Algebra.Construct.Lexicographic as Lex
  using (Lex; Lex₂)
open import RoutingLib.Algebra.Construct.Lexicographic.Magma as OpLexProperties′
--open import RoutingLib.Function
open import RoutingLib.Relation.Nullary.Construct.Add.Point renaming (∙ to invalid; [_] to valid)
open import RoutingLib.Relation.Binary.Construct.Add.Point.Equality as PointedEq
  renaming (_≈∙_ to PointedEq)
  using (∙≈∙; [_]; [≈]-injective; ≈∙-refl; ≈∙-sym; ≈∙-trans)
open import RoutingLib.Data.Path.Uncertified.Choice using (_⊓ₗₑₓ_)  --- Minₗₑₓ._⊓_
open import RoutingLib.Data.Path.Uncertified.Properties

open import RoutingLib.Algebra.Construct.NaturalChoice.Min.TotalOrder
open import RoutingLib.Data.Path.UncertifiedI using (Pathᵛ; Path; _∉ᵥₚ_; _∈ᵥₚ_; _⇿ᵥ_; _∈ₚ_; _∉ₚ_;_⇿_;_∷_ ) 

open import RoutingLib.Routing.Algebra.Construct.AddPaths A
     using (AddPaths; isRoutingAlgebra; isPathAlgebra; ⊕⁺-idem; ⊕⁺invalidᵣ; ⊕⁺invalidₗ) 


open RawRoutingAlgebra A renaming
     (Route              to Routeᴬ ; 
      Step               to Stepᴬ  ;
      _≈_                to _≈ᴬ_   ;
      _≉_                to _≉ᴬ_   ; 
      _⊕_                to _⊕ᴬ_   ; 
      _▷_                to _▷ᴬ_   ;
      0#                 to 0#ᴬ    ;
      ∞#                 to ∞#ᴬ    ; 
      f∞                 to f∞ᴬ    ;
      ≈-isDecEquivalence to ≈ᴬ-isDecEquivalence ;
      ⊕-cong             to ⊕ᴬ-cong    ; 
      ▷-cong             to ▷ᴬ-cong    ;
      f∞-reject          to f∞ᴬ-reject 
      )


open IsRoutingAlgebra A-IsRoutingAlgebra  renaming
     (⊕-sel        to ⊕ᴬ-sel        ;
      ⊕-comm       to ⊕ᴬ-comm       ;
      ⊕-assoc      to ⊕ᴬ-assoc      ;
      ⊕-zeroʳ      to ⊕ᴬ-zeroʳ       ;
      ⊕-identityʳ  to ⊕ᴬ-identityʳ   ;
      ▷-fixedPoint to ▷ᴬ-fixedPoint  
      )

open IsDecEquivalence ≈ᴬ-isDecEquivalence renaming
     (_≟_  to _≟ᴬ_    ;
      isEquivalence to ≈ᴬ-isEquivalence
     )

open IsEquivalence ≈ᴬ-isEquivalence renaming
     (refl  to ≈ᴬ-refl ;
      sym   to ≈ᴬ-sym ;
      trans to ≈ᴬ-trans
     )


no-∞-sum : ∀ {x y} → x ≉ᴬ ∞#ᴬ → y ≉ᴬ ∞#ᴬ → (x ⊕ᴬ y) ≉ᴬ ∞#ᴬ
no-∞-sum {x} {y} x≉∞ y≉∞  with ⊕ᴬ-sel x y
... | inj₁ x⊕y≈x = λ x⊕y≈∞ → contradiction (≈ᴬ-trans (≈ᴬ-sym x⊕y≈x) x⊕y≈∞) x≉∞
... | inj₂ x⊕y≈y = λ x⊕y≈∞ → contradiction (≈ᴬ-trans (≈ᴬ-sym x⊕y≈y) x⊕y≈∞) y≉∞



Aᵖ : RawRoutingAlgebra a b ℓ
Aᵖ = AddPaths ⊕-assoc ⊕-sel ⊕-comm 
     where open IsRoutingAlgebra A-IsRoutingAlgebra

open RawRoutingAlgebra Aᵖ  renaming
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
      _≤₊_               to _≤₊⁺_
     )

Aᵖ-IsRoutingAlgebra : IsRoutingAlgebra Aᵖ
Aᵖ-IsRoutingAlgebra = isRoutingAlgebra ⊕-assoc ⊕-sel ⊕-comm  A-IsRoutingAlgebra   
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
Aᵖ-IsPathAlgebra = isPathAlgebra ⊕-assoc ⊕-sel ⊕-comm 
     where open IsRoutingAlgebra A-IsRoutingAlgebra

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

cong-path-distrib : ∀ a b c d  → a ≈⁺ c → b ≈⁺ d → ∀ k
                    → IsLevel k PathDistributiveIn[ a , b ] → IsLevel k PathDistributiveIn[ c , d ]

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

∉ₚto∉̂ᴱ : ∀ {n x p} {i : Fin n}  → (toℕ i) ∉ₚ (path (valid (x , p))) → toℕ i ∉ᵥₚ p 
∉ₚto∉̂ᴱ i∉ₚ = λ z → i∉ₚ (valid z)

∈ᵥₚ=>∈ₚ : ∀ {n p} {i : Fin n} → toℕ i ∈ᵥₚ p → toℕ i ∈ₚ (valid p)
∈ᵥₚ=>∈ₚ {n} {p} {i} i∈ᵥₚp = valid i∈ᵥₚp 



cong-path-constant : ∀ k a b → a ≈⁺ b  → IsLevel k PathDistributiveIn[ a , b ]  

cong-path-constant zero  a b a≈b {n} {i} {j} f {x} {y} a≤x x≤b a≤y y≤b _ _ _ _  = goal
  where
  x≈a : x ≈⁺ a  
  x≈a = ≤₊⁺-antisym (≤₊⁺-respʳ-≈⁺ (≈⁺-sym a≈b) x≤b) a≤x 
  
  y≈b : y ≈⁺ b
  y≈b = ≤₊⁺-antisym y≤b (≤₊⁺-respˡ-≈⁺ {y} a≈b a≤y) 

  x≈y : x ≈⁺ y
  x≈y = ≈⁺-trans  x≈a (≈⁺-trans a≈b (≈⁺-sym y≈b))  

  goal : f ▷⁺ (x ⊕⁺ y) ≈⁺ ((f ▷⁺ x) ⊕⁺ (f ▷⁺ y))  
  goal = begin 
           f ▷⁺ (x ⊕⁺ y)             ≈⟨ ▷⁺-cong f (⊕⁺-cong {x} ≈⁺-refl  (≈⁺-sym x≈y)) ⟩
           f ▷⁺ (x ⊕⁺ x)             ≈⟨  ▷⁺-cong f (⊕⁺-idem ⊕ᴬ-assoc ⊕ᴬ-sel ⊕ᴬ-comm x) ⟩ 
           f ▷⁺ x                    ≈⟨ ≈⁺-sym (⊕⁺-idem ⊕ᴬ-assoc ⊕ᴬ-sel ⊕ᴬ-comm (f ▷⁺ x))  ⟩
           ((f ▷⁺ x) ⊕⁺ (f ▷⁺ x))    ≈⟨ ⊕⁺-cong {(f ▷⁺ x)}  ≈⁺-refl (▷⁺-cong f x≈y)  ⟩ 
           ((f ▷⁺ x) ⊕⁺ (f ▷⁺ y))    ∎
           where open EqReasoning (record { isEquivalence = ≈⁺-isEquivalence }) 

cong-path-constant (suc k) a b a≈b {n} {i} {j} f {x} {y} a≤x x≤b a≤y y≤b _ _  = cnc 
  where
  x≈a : x ≈⁺ a  
  x≈a = ≤₊⁺-antisym (≤₊⁺-respʳ-≈⁺ (≈⁺-sym a≈b) x≤b) a≤x 
  
  y≈b : y ≈⁺ b
  y≈b = ≤₊⁺-antisym y≤b (≤₊⁺-respˡ-≈⁺ {y} a≈b a≤y) 

  x≈y : x ≈⁺ y
  x≈y = ≈⁺-trans  x≈a (≈⁺-trans a≈b (≈⁺-sym y≈b))

  tst : f ▷⁺ (x ⊕⁺ y) ≈⁺ ((f ▷⁺ x) ⊕⁺ (f ▷⁺ y))  
  tst = begin 
           f ▷⁺ (x ⊕⁺ y)             ≈⟨ ▷⁺-cong f (⊕⁺-cong {x} ≈⁺-refl  (≈⁺-sym x≈y)) ⟩
           f ▷⁺ (x ⊕⁺ x)             ≈⟨  ▷⁺-cong f (⊕⁺-idem ⊕ᴬ-assoc ⊕ᴬ-sel ⊕ᴬ-comm x)  ⟩
           f ▷⁺ x                    ≈⟨ ≈⁺-sym (⊕⁺-idem ⊕ᴬ-assoc ⊕ᴬ-sel ⊕ᴬ-comm (f ▷⁺ x)) ⟩ 
           ((f ▷⁺ x) ⊕⁺ (f ▷⁺ x))    ≈⟨ ⊕⁺-cong {(f ▷⁺ x)}  ≈⁺-refl (▷⁺-cong f x≈y)  ⟩ 
           ((f ▷⁺ x) ⊕⁺ (f ▷⁺ y))    ∎
           where open EqReasoning (record { isEquivalence = ≈⁺-isEquivalence }) 


  cnc : IsLevel k PathDistributiveIn[ f ▷⁺ (x ⊕⁺ y) ,  (f ▷⁺ x) ⊕⁺ (f ▷⁺ y)  ]
  cnc =  cong-path-constant k (f ▷⁺ (x ⊕⁺ y)) ((f ▷⁺ x) ⊕⁺ (f ▷⁺ y))  tst   

  eqr : ∀ {x} {y} {r} {s} → ((valid (x , r)) ⊕⁺ (valid (y , s))) ≈⁺ (valid (y , s)) → (x ⊕ᴬ y) ≈ᴬ y 
  eqr {x} {y} {r} {s} h with  x ⊕ᴬ y ≟ᴬ x | x ⊕ᴬ y ≟ᴬ y
  eqr {x} {y} {r} {s} h | _ | yes p  = p
  eqr {x} {y} {r} {s} h | yes p | no _ = proj₁ ([≈]-injective _ h) 
  eqr {x} {y} {r} {s} h | no ¬p | no ¬p₁ = contradiction (proj₁ ([≈]-injective _ h)) ¬p₁

  G : Routeᴬ  → Routeᴬ  → Pathᵛ  → Pathᵛ → Pathᵛ
  G = Lex₂ _≟ᴬ_ _⊕ᴬ_  _⊓ₗₑₓ_


  Lex-G⁺ : ∀ x y p q → (valid (x , p)) ⊕⁺ (valid (y , q)) ≈⁺ valid (x ⊕ᴬ y , G x y p q)
  Lex-G⁺ x y p q =  ≈⁺-refl 

  ▷⁺-valid : ∀ {n} {i j : Fin n} (f : Step⁺ i j) x p (i∉p : toℕ i ∉ᵥₚ p) → ((toℕ i , toℕ j) ⇿ᵥ p) → (f ▷ᴬ x ≉ᴬ ∞#ᴬ) →
                            (f ▷⁺ (valid (x , p)))
                            ≈⁺
                            valid (f ▷ᴬ x , (toℕ i , toℕ j) ∷ p) 
  ▷⁺-valid {n} {i} {j} f x p i∉p ij⇿p fx≉∞ with (toℕ i , toℕ j) ⇿? p | toℕ i ∈ₚ? p | f ▷ᴬ x ≟ᴬ ∞#ᴬ
  ... | no  ¬ij⇿p | _   | _         = contradiction ij⇿p ¬ij⇿p 
  ... | yes _ | yes i∈p | _         = contradiction i∈p i∉p 
  ... | yes _ | no  _   | yes f▷x≈∞ = contradiction f▷x≈∞ fx≉∞ 
  ... | yes _ | no  _   | no  f▷x≉∞ = ≈⁺-refl  


  pres-distrib : ∀ {k ⊤ ⊥} → Level_DistributiveIn[_,_] A k ⊥ ⊤ →
                 ∀ p q → IsLevel_PathDistributiveIn[_,_] k (valid (⊥ , p)) (valid (⊤ , q))

  pres-distrib {zero} {⊤} {⊥} dist p q {n} {i} {j} f {invalid}       {invalid}       ⊥≤x x≤⊤ ⊥≤y y≤⊤ _ _ _ _    = ∙≈∙
  
  pres-distrib {zero} {⊤} {⊥} dist p q {n} {i} {j} f {valid (x , r)} {invalid}       ⊥≤x x≤⊤ ⊥≤y y≤⊤ _ _ _ _    
      with f ▷ᴬ x ≟ᴬ ∞#ᴬ | (toℕ i , toℕ j) ⇿? r  | toℕ i ∈ₚ? r 
  ... | yes  _   | _       | _           = ∙≈∙
  ... | no _     | no  _   | _           = ∙≈∙
  ... | no _     | yes _   | yes _       = ∙≈∙
  ... | no _     | yes  _  | no _        = [ (≈ᴬ-refl , _≡_.refl) ]

  pres-distrib {zero} {⊤} {⊥} dist p q {n} {i} {j} f {invalid} {valid (y , s)}        ⊥≤x x≤⊤ ⊥≤y y≤⊤ _ _ _ _ 
      with f ▷ᴬ y ≟ᴬ ∞#ᴬ | (toℕ i , toℕ j) ⇿? s  | toℕ i ∈ₚ? s 
  ... | yes _ | _     | _     = ∙≈∙
  ... | no _  | no _  | _     = ∙≈∙
  ... | no _  | yes _ | yes _ = ∙≈∙
  ... | no _  | yes _ | no _  = [ (≈ᴬ-refl , _≡_.refl) ]

  pres-distrib {zero} {⊤} {⊥} dist p q {n} {i} {j} f {valid (x , r)} {valid (y , s)} ⊥≤x x≤⊤ ⊥≤y y≤⊤ i∉r i∉s (just ij⇿r) (just ij⇿s) = prf
    where
    dst : f ▷ᴬ (x ⊕ᴬ y) ≈ᴬ (f ▷ᴬ x) ⊕ᴬ (f ▷ᴬ y)
    dst = dist f (eqr ⊥≤x) (eqr x≤⊤)  (eqr ⊥≤y) (eqr y≤⊤)
    
    prf : (f ▷⁺ (valid (x ⊕ᴬ y , G x y r s))) ≈⁺ ((f ▷⁺ (valid (x , r))) ⊕⁺ (f ▷⁺ (valid (y , s))))
    prf with f ▷ᴬ x ≟ᴬ ∞#ᴬ | f ▷ᴬ y ≟ᴬ ∞#ᴬ | f ▷ᴬ (x ⊕ᴬ y) ≟ᴬ ∞#ᴬ
    prf | yes _ | yes _ | yes _ = ∙≈∙
    prf | yes f▷x=∞ | yes f▷y=∞ | no ¬f▷x⊕y=∞ = contradiction f▷x⊕y≈∞ ¬f▷x⊕y=∞
      where
      f▷x⊕y≈∞ : f ▷ᴬ (x ⊕ᴬ y) ≈ᴬ ∞#ᴬ
      f▷x⊕y≈∞ = begin 
           f ▷ᴬ (x ⊕ᴬ y)              ≈⟨ dst ⟩
           (f ▷ᴬ x) ⊕ᴬ (f ▷ᴬ y)       ≈⟨ ⊕ᴬ-cong f▷x=∞ f▷y=∞   ⟩ -- 
           ∞#ᴬ ⊕ᴬ ∞#ᴬ                 ≈⟨ ⊕ᴬ-identityʳ _ ⟩                      
           ∞#ᴬ                        ∎
           where open EqReasoning (record { isEquivalence = ≈ᴬ-isEquivalence })
           
    prf | yes f▷x=∞ | no ¬f▷y=∞ | yes f▷x⊕y=∞ = contradiction f▷y≈∞ ¬f▷y=∞
      where
      f▷y≈∞ : f ▷ᴬ y ≈ᴬ ∞#ᴬ
      f▷y≈∞ = begin 
           f ▷ᴬ y                    ≈⟨ ≈ᴬ-sym (⊕ᴬ-identityʳ _) ⟩
           (f ▷ᴬ y) ⊕ᴬ ∞#ᴬ           ≈⟨ ⊕ᴬ-comm _ _ ⟩           
           ∞#ᴬ ⊕ᴬ (f ▷ᴬ y)            ≈⟨ ⊕ᴬ-cong (≈ᴬ-sym f▷x=∞) ≈ᴬ-refl ⟩
           (f ▷ᴬ x) ⊕ᴬ (f ▷ᴬ y)       ≈⟨ ≈ᴬ-sym dst ⟩ --            
           f ▷ᴬ (x ⊕ᴬ y)              ≈⟨ f▷x⊕y=∞ ⟩                      
           ∞#ᴬ                        ∎
           where open EqReasoning (record { isEquivalence = ≈ᴬ-isEquivalence }) 

    prf | no ¬f▷x=∞ | yes f▷y=∞ | yes f▷x⊕y=∞ = contradiction f▷x≈∞ ¬f▷x=∞
      where
      f▷x≈∞ : f ▷ᴬ x ≈ᴬ ∞#ᴬ
      f▷x≈∞ = begin 
           f ▷ᴬ x                    ≈⟨ ≈ᴬ-sym (⊕ᴬ-identityʳ _) ⟩
           (f ▷ᴬ x) ⊕ᴬ ∞#ᴬ           ≈⟨ ⊕ᴬ-cong ≈ᴬ-refl (≈ᴬ-sym f▷y=∞)  ⟩
           (f ▷ᴬ x) ⊕ᴬ (f ▷ᴬ y)       ≈⟨ ≈ᴬ-sym dst ⟩ --            
           f ▷ᴬ (x ⊕ᴬ y)              ≈⟨ f▷x⊕y=∞ ⟩                      
           ∞#ᴬ                        ∎
           where open EqReasoning (record { isEquivalence = ≈ᴬ-isEquivalence })
--  
    prf | yes f▷x=∞ | no ¬f▷y=∞ | no ¬f▷x⊕y=∞
       with (toℕ i , toℕ j) ⇿? (G x y r s) | (toℕ i , toℕ j) ⇿? r | (toℕ i , toℕ j) ⇿? s
    ...   | _ | _ | no ¬p = contradiction ij⇿s ¬p       
    ...   | _ | no ¬p | _ = contradiction ij⇿r ¬p
    ...   | no ¬p | yes p | yes p₁ = {!!} --- need lemma : (toℕ i , toℕ j) ⇿? r -> (toℕ i , toℕ j) ⇿? s -> ... 
    ...   | yes p | yes p₁ | yes p₂
        with toℕ i ∈ₚ? (G x y r s) | toℕ i ∈ₚ? r | toℕ i ∈ₚ? s
    ...    | _ | _ | yes i∈ₚs = contradiction (∈ᵥₚ=>∈ₚ i∈ₚs) i∉s
    ...    | _ | yes i∈ₚr | _ = contradiction (∈ᵥₚ=>∈ₚ i∈ₚr) i∉r
    ...    | yes p₃ | no ¬p | no ¬p₁ = {!!} --- need lemma : (toℕ i , toℕ j) ⇿? r -> (toℕ i , toℕ j) ⇿? s -> ... 
    ...    | no i∉ₚG | no i∉ₚr | no i∉ₚs = lem 
         where
         f▷x⊕y=f▷y : f ▷ᴬ (x ⊕ᴬ y) ≈ᴬ f ▷ᴬ y
         f▷x⊕y=f▷y = begin 
           f ▷ᴬ (x ⊕ᴬ y)              ≈⟨ dst ⟩
           (f ▷ᴬ x) ⊕ᴬ (f ▷ᴬ y)       ≈⟨ ⊕ᴬ-cong f▷x=∞ ≈ᴬ-refl ⟩
           ∞#ᴬ ⊕ᴬ (f ▷ᴬ y)            ≈⟨ ⊕ᴬ-comm _ _ ⟩
           (f ▷ᴬ y) ⊕ᴬ ∞#ᴬ            ≈⟨ ⊕ᴬ-identityʳ _ ⟩                                 
           (f ▷ᴬ y)                   ∎
           where open EqReasoning (record { isEquivalence = ≈ᴬ-isEquivalence })
         
         lem : valid (f ▷ᴬ (x ⊕ᴬ y) , (toℕ i , toℕ j) ∷ (G x y r s)) ≈⁺ valid (f ▷ᴬ y , (toℕ i , toℕ j) ∷ s)
         lem = begin 
               valid (f ▷ᴬ (x ⊕ᴬ y) , (toℕ i , toℕ j) ∷ (G x y r s)) ≈⟨ [ (f▷x⊕y=f▷y , _≡_.refl) ] ⟩
               valid (f ▷ᴬ y , (toℕ i , toℕ j) ∷ (G x y r s))        ≈⟨ [ (≈ᴬ-refl , {!!}) ] ⟩ -- need lemma 
               valid (f ▷ᴬ y , (toℕ i , toℕ j) ∷ s)   ∎
               where open EqReasoning (record { isEquivalence = ≈⁺-isEquivalence }) 

    prf | no ¬f▷x=∞ | yes f▷y=∞ | no ¬f▷x⊕y=∞ 
       with (toℕ i , toℕ j) ⇿? (G x y r s) | (toℕ i , toℕ j) ⇿? r | (toℕ i , toℕ j) ⇿? s
    ...   | _ | _ | no ¬p = contradiction ij⇿s ¬p       
    ...   | _ | no ¬p | _ = contradiction ij⇿r ¬p
    ...   | no ¬p | yes p | yes p₁ = {!!} --- need lemma : (toℕ i , toℕ j) ⇿? r -> (toℕ i , toℕ j) ⇿? s -> ... 
    ...   | yes p | yes p₁ | yes p₂
        with toℕ i ∈ₚ? (G x y r s) | toℕ i ∈ₚ? r | toℕ i ∈ₚ? s
    ...    | _ | _ | yes i∈ₚs = contradiction (∈ᵥₚ=>∈ₚ i∈ₚs) i∉s
    ...    | _ | yes i∈ₚr | _ = contradiction (∈ᵥₚ=>∈ₚ i∈ₚr) i∉r
    ...    | yes p₃ | no ¬p | no ¬p₁ = {!!} --- need lemma : (toℕ i , toℕ j) ⇿? r -> (toℕ i , toℕ j) ⇿? s -> ... 
    ...    | no i∉ₚG | no i∉ₚr | no i∉ₚs = lem 
         where
         f▷x⊕y=f▷x : f ▷ᴬ (x ⊕ᴬ y) ≈ᴬ f ▷ᴬ x
         f▷x⊕y=f▷x = begin 
           f ▷ᴬ (x ⊕ᴬ y)              ≈⟨ dst ⟩
           (f ▷ᴬ x) ⊕ᴬ (f ▷ᴬ y)       ≈⟨ ⊕ᴬ-cong ≈ᴬ-refl f▷y=∞  ⟩
           (f ▷ᴬ x) ⊕ᴬ ∞#ᴬ            ≈⟨ ⊕ᴬ-identityʳ _ ⟩                                 
           (f ▷ᴬ x)                   ∎
           where open EqReasoning (record { isEquivalence = ≈ᴬ-isEquivalence })
         
         lem : valid (f ▷ᴬ (x ⊕ᴬ y) , (toℕ i , toℕ j) ∷ (G x y r s)) ≈⁺ valid (f ▷ᴬ x , (toℕ i , toℕ j) ∷ r)
         lem = begin 
               valid (f ▷ᴬ (x ⊕ᴬ y) , (toℕ i , toℕ j) ∷ (G x y r s)) ≈⟨ [ (f▷x⊕y=f▷x , _≡_.refl) ] ⟩
               valid (f ▷ᴬ x , (toℕ i , toℕ j) ∷ (G x y r s))        ≈⟨ [ (≈ᴬ-refl , {!!}) ] ⟩ -- need lemma 
               valid (f ▷ᴬ x , (toℕ i , toℕ j) ∷ r)   ∎
               where open EqReasoning (record { isEquivalence = ≈⁺-isEquivalence }) 

    prf | no f▷x≉∞ | no f▷y≉∞ | yes f▷x⊕y≈∞ = contradiction f▷x⊕f▷y≈∞ f▷x⊕f▷y≉∞
      where
      f▷x⊕f▷y≉∞ : (f ▷ᴬ x) ⊕ᴬ (f ▷ᴬ y) ≉ᴬ ∞#ᴬ
      f▷x⊕f▷y≉∞ = no-∞-sum f▷x≉∞ f▷y≉∞
      
      f▷x⊕f▷y≈∞  : (f ▷ᴬ x) ⊕ᴬ (f ▷ᴬ y) ≈ᴬ ∞#ᴬ 
      f▷x⊕f▷y≈∞ = ≈ᴬ-trans (≈ᴬ-sym dst) f▷x⊕y≈∞

    prf | no ¬f▷x=∞ | no ¬f▷y=∞ | no ¬f▷x⊕y=∞
       with (toℕ i , toℕ j) ⇿? (G x y r s) | (toℕ i , toℕ j) ⇿? r | (toℕ i , toℕ j) ⇿? s
    ...   | _ | _ | no ¬p = contradiction ij⇿s ¬p       
    ...   | _ | no ¬p | _ = contradiction ij⇿r ¬p
    ...   | no ¬p | yes p | yes p₁ = {!!} --- need lemma : (toℕ i , toℕ j) ⇿? r -> (toℕ i , toℕ j) ⇿? s -> ... 
    ...   | yes p | yes p₁ | yes p₂ 
        with toℕ i ∈ₚ? (G x y r s) | toℕ i ∈ₚ? r | toℕ i ∈ₚ? s
    ...    | _ | _ | yes i∈ₚs = contradiction (∈ᵥₚ=>∈ₚ i∈ₚs) i∉s
    ...    | _ | yes i∈ₚr | _ = contradiction (∈ᵥₚ=>∈ₚ i∈ₚr) i∉r
    ...    | yes p₃ | no ¬p | no ¬p₁ = {!!} --- need lemma : (toℕ i , toℕ j) ⇿? r -> (toℕ i , toℕ j) ⇿? s -> ... 
    ...    | no i∉ₚG | no i∉ₚr | no i∉ₚs = lem 
         where
         lem : valid (f ▷ᴬ (x ⊕ᴬ y) , (toℕ i , toℕ j) ∷ (G x y r s))
               ≈⁺
               valid (f ▷ᴬ x , (toℕ i , toℕ j) ∷ r) ⊕⁺ valid (f ▷ᴬ y , (toℕ i , toℕ j) ∷ s)
         lem = begin 
               valid (f ▷ᴬ (x ⊕ᴬ y) , (toℕ i , toℕ j) ∷ (G x y r s)) ≈⟨ [ (dst , _≡_.refl) ] ⟩
               valid ((f ▷ᴬ x) ⊕ᴬ (f ▷ᴬ y) , (toℕ i , toℕ j) ∷ (G x y r s)) ≈⟨ [ (≈ᴬ-refl , {!!}) ] ⟩ --- lemma 
               valid ((f ▷ᴬ x) ⊕ᴬ (f ▷ᴬ y) , G x y ((toℕ i , toℕ j) ∷ r) ((toℕ i , toℕ j) ∷ s)) ≈⟨ {!!} ⟩   -- lemma
               valid (f ▷ᴬ x , (toℕ i , toℕ j) ∷ r) ⊕⁺ valid (f ▷ᴬ y , (toℕ i , toℕ j) ∷ s)   ∎
               where open EqReasoning (record { isEquivalence = ≈⁺-isEquivalence }) 
    


{-  
     i∉ᵥGxyrs : toℕ i ∉ᵥₚ G x y r s
     i∉ᵥGxyrs = {!!}  -- (Lex-G-∉̂ᴱ  x  y  r s ( (∉ₚto∉̂ᴱ {n} {x} {r} {i} i∉r) ) ( (∉ₚto∉̂ᴱ {n} {y}  {s} {i} i∉s)))

     ij⇿Gxyrs : (toℕ i , toℕ j) ⇿ᵥ G x y r s
     ij⇿Gxyrs = {!!}
     
     cnc : f ▷⁺ ((valid (x , r)) ⊕⁺ (valid (y , s))) ≈⁺ ((f ▷⁺ (valid (x , r))) ⊕⁺ (f ▷⁺ (valid (y , s))))
     cnc = begin 
           f ▷⁺ ((valid (x , r)) ⊕⁺ (valid (y , s)))
             ≈⟨  ▷⁺-cong f ((Lex-G⁺ x y r s)) ⟩
           f ▷⁺ (valid (x ⊕ y , G x y r s))
             ≈⟨  ▷⁺-valid f _ _  i∉ᵥGxyrs ij⇿Gxyrs f▷x+y≉∞  ⟩ 
           valid (f ▷ (x ⊕ y) , (toℕ i , toℕ j)  ∷  (G x y r s))
             ≈⟨ [ (dst , refl) ] ⟩ 
           valid ((f ▷ x) ⊕ (f ▷ y) , (toℕ i , toℕ j) ∷ (G x y r s))
             ≈⟨ [ (≈-refl , G-cons-dist x y r s) ] ⟩
           valid ((f ▷ x) ⊕ (f ▷ y) ,  (G x y ((toℕ i , toℕ j) ∷ r) ((toℕ i , toℕ j) ∷ s)))
             ≈⟨ [ (≈-refl , {!!}) ] ⟩ -- cong, sym, and Lex-G⁺
           valid ((f ▷ x) ⊕ (f ▷ y) ,  (G (f ▷ x) (f ▷ y) ((toℕ i , toℕ j) ∷ r) ((toℕ i , toℕ j) ∷ s)))
             ≈⟨ ≈⁺-sym (Lex-G⁺ (f ▷ x) (f ▷ y) ((toℕ i , toℕ j) ∷ r) ((toℕ i , toℕ j) ∷ s)) ⟩ 
           valid (f ▷ x , (toℕ i , toℕ j) ∷ r) ⊕⁺ valid (f ▷ y , (toℕ i , toℕ j) ∷ s)
             ≈⟨ ⊕⁺-cong (≈⁺-sym (▷⁺-valid f x r (λ z → i∉r (valid z)) ij⇿r f▷x≉∞ )) ≈⁺-refl ⟩ 
           (f ▷⁺ (valid (x , r))) ⊕⁺ valid (f ▷ y , (toℕ i , toℕ j) ∷ s)
             ≈⟨ ⊕⁺-cong {(f ▷⁺ (valid (x , r)))}  ≈⁺-refl  (≈⁺-sym (▷⁺-valid f y s (λ z → i∉s (valid z)) ij⇿s f▷y≉∞))  ⟩ 
           (f ▷⁺ (valid (x , r))) ⊕⁺ (f ▷⁺ (valid (y , s)))                                     ∎
           where open EqReasoning (record { isEquivalence = ≈⁺-isEquivalence })  
-}

  pres-distrib {suc k} {⊤} {⊥} dist p q {n} {i} {j} f {invalid}       {invalid}       ⊥≤x x≤⊤ ⊥≤y y≤⊤ _ _     = prf
    where
    prf : IsLevel k PathDistributiveIn[ invalid , invalid ]
    prf = cong-path-constant k invalid invalid  ≈⁺-refl 
  
  pres-distrib {suc k} {⊤} {⊥} dist p q {n} {i} {j} f {valid (x , r)} {invalid}       ⊥≤x x≤⊤ ⊥≤y y≤⊤ i∉r _ = prf
    where 
    lem : f ▷⁺ ((valid (x , r)) ⊕⁺ invalid) ≈⁺ (f ▷⁺ (valid (x , r))) ⊕⁺ (f ▷⁺ invalid)
    lem  = begin
           f ▷⁺ ((valid (x , r)) ⊕⁺ invalid)        ≈⟨ ▷⁺-cong f ≈⁺-refl ⟩
           f ▷⁺ (valid (x , r))                     ≈⟨ ≈⁺-sym (⊕⁺-identityʳ _) ⟩
           (f ▷⁺ (valid (x , r))) ⊕⁺ invalid        ≈⟨ ⊕⁺-cong {(f ▷⁺ (valid (x , r)))} ≈⁺-refl ≈⁺-refl  ⟩                      
           (f ▷⁺ (valid (x , r))) ⊕⁺ (f ▷⁺ invalid) ∎
           where open EqReasoning (record { isEquivalence = ≈⁺-isEquivalence })
           

    prf : IsLevel k PathDistributiveIn[ f ▷⁺ ((valid (x , r)) ⊕⁺ invalid) , (f ▷⁺ (valid (x , r))) ⊕⁺ (f ▷⁺ invalid) ]
    prf = cong-path-constant k _ _ lem

  
  pres-distrib {suc k} {⊤} {⊥} dist p q {_} {i} {j} f {invalid} {valid (y , s)}        ⊥≤x x≤⊤ ⊥≤y y≤⊤ _ i∉s = prf
    where
    lem : f ▷⁺ (invalid ⊕⁺ (valid (y , s)) ) ≈⁺ (f ▷⁺ invalid) ⊕⁺ (f ▷⁺ (valid (y , s)))
    lem = begin
           f ▷⁺ (invalid ⊕⁺ (valid (y , s)) )      ≈⟨ ▷⁺-cong f ≈⁺-refl ⟩
           f ▷⁺ (valid (y , s))                    ≈⟨ ≈⁺-refl ⟩
           invalid ⊕⁺ (f ▷⁺ (valid (y , s)))       ≈⟨ ≈⁺-refl ⟩                     
           (f ▷⁺ invalid) ⊕⁺ (f ▷⁺ (valid (y , s))) ∎
           where open EqReasoning (record { isEquivalence = ≈⁺-isEquivalence })
    
    prf : IsLevel k PathDistributiveIn[ f ▷⁺ (invalid ⊕⁺ (valid (y , s)) ) , (f ▷⁺ invalid) ⊕⁺ (f ▷⁺ (valid (y , s))) ]    
    prf = cong-path-constant k _ _ lem

  
  pres-distrib {suc k} {⊤} {⊥} dist p q {_} {i} {j} f {valid (x , r)} {valid (y , s)}       ⊥≤x x≤⊤ ⊥≤y y≤⊤ i∉r i∉s
    with f ▷ᴬ x ≟ᴬ ∞#ᴬ | f ▷ᴬ y ≟ᴬ ∞#ᴬ | f ▷ᴬ (x ⊕ᴬ y) ≟ᴬ ∞#ᴬ
  ... | yes p₁ | yes p₂ | yes p₃ = prf
    where
    prf : IsLevel k PathDistributiveIn[ invalid , invalid ] 
    prf = {!!}
    
  ... | yes f▷x≈∞ | yes f▷y≈∞ | no f▷x⊕y≉∞ = {!!}
  ... | yes p₁ | no ¬p | yes p₂ = {!!}
  ... | yes p₁ | no ¬p | no ¬p₁ = {!!}
  ... | no ¬p | yes p₁ | yes p₂ = {!!}
  ... | no ¬p | yes p₁ | no ¬p₁ = {!!}
  ... | no ¬p | no ¬p₁ | yes p₁ = {!!}
  ... | no ¬p | no ¬p₁ | no ¬p₂ 
    with (toℕ i , toℕ j) ⇿? (G x y r s) | (toℕ i , toℕ j) ⇿? r | (toℕ i , toℕ j) ⇿? s
  ...  | yes q₁ | yes q₂ | no ¬q₃ = {!!}
  ...  | yes q₁ | no ¬q₃ | yes q₂ = {!!}
  ...  | yes q₁ | no ¬q₃ | no ¬q₄ = {!!}
  ...  | no ¬q₃ | yes q₁ | yes q₂ = {!!}
  ...  | no ¬q₃ | yes q₁ | no ¬q₄ = {!!}
  ...  | no ¬q₃ | no ¬q₄ | yes q₁ = {!!}
  ...  | no ¬q₃ | no ¬q₄ | no ¬q₅ = {!!}
  ...  | yes q₁ | yes q₂ | yes q₃
    with toℕ i ∈ₚ? (G x y r s) | toℕ i ∈ₚ? r | toℕ i ∈ₚ? s
  ... | yes z₁ | yes z₂ | yes z₃ = {!!}    
  ... | yes z₁ | yes z₂ | no ¬z₃ = {!!}
  ... | yes z₁ | no ¬z₃ | yes z₂ = {!!}
  ... | yes z₁ | no ¬z₃ | no ¬z₄ = {!!}
  ... | no ¬z₃ | yes z₁ | yes z₂ = {!!}
  ... | no ¬z₃ | yes z₁ | no ¬z₄ = {!!}
  ... | no ¬z₃ | no ¬z₄ | yes z₁ = {!!}
  ... | no ¬z₃ | no ¬z₄ | no ¬z₅ = prf
    where
    prf : IsLevel k PathDistributiveIn[ valid (f ▷ᴬ (x ⊕ᴬ y)  , (toℕ i , toℕ j) ∷ (Lex₂ _≟ᴬ_ _⊕ᴬ_ _⊓ₗₑₓ_ x y r s)) , 
                                        valid (Lex _≟ᴬ_ _⊕ᴬ_ _⊓ₗₑₓ_ (f ▷ᴬ x , (toℕ i , toℕ j) ∷ r) (f ▷ᴬ y , (toℕ i , toℕ j) ∷ s))
                                       ]
    prf = cong-path-distrib _ _ _ _ {!!} {!!}  k (pres-distrib {k} {_} {_} (dist f (eqr ⊥≤x) (eqr x≤⊤)  (eqr ⊥≤y) (eqr y≤⊤)) _ _)

  
{- 
    wherepppp
    dst : Level A DistributiveIn[ k , f ▷ᴬ (x ⊕ᴬ y) ] ((f ▷ᴬ x) ⊕ᴬ (f ▷ᴬ y))
    dst = dist f (eqr ⊥≤x) (eqr x≤⊤)  (eqr ⊥≤y) (eqr y≤⊤)

    ind : IsLevel k PathDistributiveIn[ valid (f ▷ᴬ (x ⊕ᴬ y) , (toℕ i , toℕ j) ∷ (G x y r s)) , 
                                        valid ((f ▷ᴬ x) ⊕ᴬ (f ▷ᴬ y) , G x y ((toℕ i , toℕ j) ∷ r) ((toℕ i , toℕ j) ∷ s) )
                                      ]                                          
    ind = pres-distrib {k} {_} {_} dst _ _

    --- need : toℕ i ∉ᵥₚ G x y r s    (toℕ i , toℕ j) ⇿ᵥ G x y r s        f ▷ᴬ (x ⊕ᴬ y) ≉ᴬ ∞#ᴬ
    eq1 : valid ( f ▷ᴬ (x ⊕ᴬ y) , (toℕ i , toℕ j) ∷ (G x y r s))  ≈⁺ f ▷⁺ ((valid (x , r)) ⊕⁺ (valid (y , s)) ) 
    eq1 = begin

           valid ( f ▷ᴬ (x ⊕ᴬ y) , (toℕ i , toℕ j) ∷ (G x y r s))    ≈⟨ ≈⁺-sym (▷⁺-valid f {!!} {!!} {!!} {!!} {!!} ) ⟩
           f ▷⁺ (valid (x ⊕ᴬ y , (G x y r s)))                          ≈⟨ ▷⁺-cong f (≈⁺-sym ≈⁺-refl) ⟩
           f ▷⁺ ((valid (x , r)) ⊕⁺ (valid (y , s))) ∎
           where open EqReasoning (record { isEquivalence = ≈⁺-isEquivalence })

-- need f ▷ᴬ (x ⊕ᴬ y) = (f ▷ᴬ x) ⊕ᴬ (f ▷ᴬ y)    toℕ i ∉ᵥₚ G x y r s      (toℕ i , toℕ j) ⇿ᵥ G x y r s    f ▷ᴬ x ⊕ᴬ y ≉ᴬ ∞#ᴬ
    eq2 : valid ( ((f ▷ᴬ x) ⊕ᴬ (f ▷ᴬ y)) , G x y ((toℕ i , toℕ j) ∷ r) ((toℕ i , toℕ j) ∷ s) )
          ≈⁺
          (f ▷⁺ (valid (x , r))) ⊕⁺ (f ▷⁺ (valid (y , s)))
    eq2 = begin
          valid ( ((f ▷ᴬ x) ⊕ᴬ (f ▷ᴬ y)) , G x y ((toℕ i , toℕ j) ∷ r) ((toℕ i , toℕ j) ∷ s) ) ≈⟨ [ (≈ᴬ-refl , {!!}) ]  ⟩ -- [ ≈-refl , {!!} ]
          valid ((f ▷ᴬ x) ⊕ᴬ (f ▷ᴬ y) , (toℕ i , toℕ j) ∷ (G x y r s))                            ≈⟨ [ ({!!} , {!!}) ] ⟩ 
          valid (f ▷ᴬ (x ⊕ᴬ y) , (toℕ i , toℕ j)  ∷  (G x y r s))                                ≈⟨ ≈⁺-sym (▷⁺-valid f {!!} {!!} {!!} {!!} {!x!})  ⟩ --  (▷⁺-valid f _ _ i∉ᵥGxyrs ij⇿Gxyrs f▷x+y≉∞ )  
          f ▷⁺ (valid (x ⊕ᴬ y , G x y r s))                                                        ≈⟨ {! !} ⟩ -- ▷⁺-cong f (≈⁺-sym (Lex-G⁺ x y r s))
          (f ▷⁺ (valid (x , r))) ⊕⁺ (f ▷⁺ (valid (y , s))) ∎
          where open EqReasoning (record { isEquivalence = ≈⁺-isEquivalence })
          
    prf :  IsLevel k PathDistributiveIn[ f ▷⁺ (valid (x , r) ⊕⁺ valid (y , s)) , (f ▷⁺ valid (x , r)) ⊕⁺ (f ▷⁺ valid (y , s)) ]
    prf = cong-path-distrib _ _ _ _ eq1 eq2 k ind  

-} 






{-

  Lex-G-∉̂ᴱ : ∀ {n} {i : Fin n} x y p q (i∉p : toℕ i ∉̂ᴱ p) (i∉q : toℕ i ∉̂ᴱ q) → toℕ i ∉̂ᴱ (G x y p q)
  Lex-G-∉̂ᴱ {n} {i} x y p q i∉p i∉q with x ⊕ y ≟ x  | x ⊕ y ≟ y | ⊓ₗₑₓ-sel p q
  ... | yes _ | yes _ | inj₁ x₁ = ∉ₚ-resp-≈ₚ (sym x₁) i∉p
  ... | yes _ | yes _ | inj₂ y₁ = ∉ₚ-resp-≈ₚ (sym y₁) i∉q
  ... | yes _ | no _  | _ = i∉p
  ... | no _  | yes _ | _ = i∉q
  ... | no _  | no _  | inj₁ x₁ = ∉ₚ-resp-≈ₚ (sym x₁) i∉p
  ... | no _  | no _  | inj₂ y₁ = ∉ₚ-resp-≈ₚ (sym y₁) i∉q


  G-cons-dist : ∀ {n} {i j : Fin n} x y p q →  (toℕ i , toℕ j) ∷ (G x y p q) ≡ (G x y ((toℕ i , toℕ j) ∷ p) ((toℕ i , toℕ j) ∷ q)) 
  G-cons-dist {n} {i} {j} x y p q with x ⊕ y ≟ x  | x ⊕ y ≟ y 
  ... | yes _ | yes _ = ∷-distrib-⊓ₗₑₓ (toℕ i , toℕ j) p q 
  ... | yes _ | no _  = refl 
  ... | no _  | yes _ = refl 
  ... | no _  | no _  = ∷-distrib-⊓ₗₑₓ (toℕ i , toℕ j) p q 

  eql : ∀ {x} {y} {r} {s} → ((valid (x , r)) ⊕⁺ (valid (y , s))) ≈⁺ (valid (x , r)) → (x ⊕ y) ≈ x
  eql {x} {y} {r} {s} h with  x ⊕ y ≟ x | x ⊕ y ≟ y
  eql {x} {y} {r} {s} h | yes p | _ = p
  eql {x} {y} {r} {s} h | no _  | yes p  = ≈-trans p (proj₁ ([≈]-injective _ h))
  eql {x} {y} {r} {s} h | no ¬p | no ¬p₁ = contradiction (proj₁ ([≈]-injective _ h)) ¬p 


  ▷⁺-reject : ∀ {n} {i j : Fin n} (f : Step i j) x p → f ▷ x ≈ ∞# → f ▷⁺ (valid (x , p)) ≈⁺ ∞#⁺
  ▷⁺-reject {_} {i} {j} f x p f▷x≈∞ with (toℕ i , toℕ j) ⇿? p | toℕ i ∈ₚ? p | f ▷ x ≟ ∞#
  ... | no  _ | _     | _         = ∙≈∙
  ... | yes _ | yes _ | _         = ∙≈∙
  ... | yes _ | no  _ | yes _     = ∙≈∙
  ... | yes _ | no  _ | no  f▷x≉∞ = contradiction f▷x≈∞ f▷x≉∞

  ▷⁺-accept : ∀ {n} {i j : Fin n} (f : Step i j) x p →
            (toℕ i , toℕ j) ⇿ᴱ p → toℕ i ∉̂ᴱ p → f ▷ x ≉ ∞# →
            f ▷⁺ (valid (x , p)) ≈⁺ valid (f ▷ x , (toℕ i , toℕ j) ∷ p)
  ▷⁺-accept {_} {i} {j} f x p ij⇿p i∉p f▷x≉∞ with (toℕ i , toℕ j) ⇿? p | toℕ i ∈ₚ? p | f ▷ x ≟ ∞#
  ... | no ¬ij⇿p | _       | _         = contradiction ij⇿p ¬ij⇿p
  ... | yes _    | yes i∈p | _         = contradiction i∈p i∉p
  ... | yes _    | no  _   | yes f▷x≈∞ = contradiction f▷x≈∞ f▷x≉∞
  ... | yes _    | no  _   | no  _     = [ ≈-refl , refl ]

-}


{-

  alt-cong-path-constant : ∀ k a b → a ≈⁺ b  → AltLevel k PathDistributiveIn[ a , b ]

  alt-cong-path-constant zero  a b a≈⁺b = {! !} 
  alt-cong-path-constant (suc k) a b a≈⁺b {n} {i} {j} f {x} {y} a≤₊x x≤₊a b≤₊y y≤₊b fx≉∞ fy≉∞ = cnc 
    where
    x≈⁺a : x ≈⁺ a
    x≈⁺a = {!!} 

    y≈⁺b : y ≈⁺ b
    y≈⁺b = {!!} 

    x≈⁺y : x ≈⁺ y
    x≈⁺y = {!!}

  
    tst : f ▷⁺ (x ⊕⁺ y) ≈⁺ ((f ▷⁺ x) ⊕⁺ (f ▷⁺ y))  
    tst = {!!}  --- need idempotence, eq-reasoning over ≈⁺
  
    cnc : AltLevel k PathDistributiveIn[ f ▷⁺ (x ⊕⁺ y) ,  (f ▷⁺ x) ⊕⁺ (f ▷⁺ y)  ]
    cnc =  alt-cong-path-constant k (f ▷⁺ (x ⊕⁺ y)) ((f ▷⁺ x) ⊕⁺ (f ▷⁺ y))  tst   

  pres-distrib : ∀ {k ⊤ ⊥} → AltLevel_DistributiveIn[_,_] A k ⊥ ⊤ →
                 ∀ p q → AltLevel k PathDistributiveIn[ valid (⊥ , p) , valid (⊤ , q) ] 
  pres-distrib {zero} {⊤} {⊥} dist p q = {!!}
  pres-distrib {suc k} {⊤} {⊥} dist p q = {!!}   
-} 
