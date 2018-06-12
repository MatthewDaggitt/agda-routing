open import Data.Fin using (Fin)
open import Data.Fin.Properties using () renaming (_≟_ to _≟F_)
open import Data.Nat using (ℕ; zero; suc; _≤_; _<_)
open import Data.Nat.Properties using (<⇒≢; <⇒≤; ≤-reflexive)
open import Data.List using (List; []; _∷_; map; filter; concat; allFin; applyUpTo)
open import Data.List.Any using (here; there)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Setoid.Properties using (∈-map⁺; ∈-concat⁺′; ∈-applyUpTo⁺)
open import Data.List.All using (All; []; _∷_) renaming (map to mapₐ)
open import Data.List.All.Properties using (applyUpTo⁺₁; applyUpTo⁺₂; concat⁺) 
open import Data.Product using (∃₂; ∃; _,_; _×_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary using (Setoid; DecSetoid; _Respects_)
open import Relation.Binary.List.Pointwise using () renaming (setoid to listSetoid)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; cong; cong₂) renaming (setoid to ≡-setoid; refl to ≡-refl; sym to ≡-sym; trans to ≡-trans)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Function using (_∘_)

open import RoutingLib.Data.List using (allFinPairs)
open import RoutingLib.Data.List.Membership.Propositional.Properties using (∈-allFin⁺; ∈-combine⁺; ∈-allFinPairs⁺)
open import RoutingLib.Data.SimplePath.NonEmpty hiding (_∈_)
open import RoutingLib.Data.SimplePath.NonEmpty.Properties
open import RoutingLib.Data.SimplePath.NonEmpty.Relation.Equality


module RoutingLib.Data.SimplePath.NonEmpty.Enumeration (n : ℕ) where

  -- Enumerating paths

  private

    Fₛ : Setoid _ _
    Fₛ = ≡-setoid (Fin n)

    F×Fₛ : Setoid _ _
    F×Fₛ = ≡-setoid (Fin n × Fin n)
    
    Pₛ : Setoid _ _
    Pₛ = ℙₛ n

    DPₛ : DecSetoid _ _
    DPₛ = ℙₛ? n

    LPₛ : Setoid _ _
    LPₛ = listSetoid Pₛ

    open import Data.List.Membership.Setoid Pₛ using () renaming (_∈_ to _∈ₚ_; _∉_ to _∉ₚ_)
    open import RoutingLib.Data.List.Relation.Disjoint   Pₛ using () renaming (_#_ to _#ₚ_)
    open import RoutingLib.Data.List.Uniqueness.Setoid Pₛ using () renaming (Unique to Uniqueₚ)
    open Setoid LPₛ using () renaming (reflexive to ≈ₗₚ-reflexive)
    

  abstract
  
    extendAll : List (SimplePathⁿᵗ n) → (Fin n × Fin n) → List (SimplePathⁿᵗ n)
    extendAll []       _       = []
    extendAll (p ∷ ps) (i , j) with (i , j) ⇿? p | i ∉? p
    ... | no  _   | _       = extendAll ps (i , j)
    ... | yes e⇿p | no  i∈p = extendAll ps (i , j)
    ... | yes e⇿p | yes i∉p = ((i , j) ∷ p ∣ e⇿p ∣ i∉p) ∷ extendAll ps (i , j)

    -- extensions

    ∈-extendAll : ∀ {e q e⇿q e∉q ps} → q ∈ₚ ps → e ∷ q ∣ e⇿q ∣ e∉q ∈ₚ extendAll ps e
    ∈-extendAll {i , j} {_} {e⇿q} {i∉q} {p ∷ _} (here q≈p) with (i , j) ⇿? p | i ∉? p
    ... | no ¬e⇿p | _       = contradiction (⇿-resp-≈ₚ q≈p e⇿q) ¬e⇿p
    ... | yes e⇿p | no  i∈p = contradiction (∉-resp-≈ₚ q≈p i∉q) i∈p
    ... | yes e⇿p | yes i∉p = here (≡-refl ∷ q≈p)
    ∈-extendAll {i , j} {ps = p ∷ _} (there q∈ps) with (i , j) ⇿? p | i ∉? p
    ... | no  _   | _       = ∈-extendAll q∈ps
    ... | yes e⇿p | no  i∈p = ∈-extendAll q∈ps
    ... | yes e⇿p | yes i∉p = there (∈-extendAll q∈ps)

    extendAll-∈ : ∀ {e v} ps → v ∈ₚ extendAll ps e → ∃ λ q → ∃₂ λ e⇿q e∉q → v ≈ₚ e ∷ q ∣ e⇿q ∣ e∉q
    extendAll-∈ []  ()
    extendAll-∈ {i , j} (p ∷ ps) v∈e[p∷ps] with (i , j) ⇿? p | i ∉? p
    ... | no  _   | _       = extendAll-∈ ps v∈e[p∷ps]
    ... | yes _   | no  _   = extendAll-∈ ps v∈e[p∷ps]
    ... | yes e⇿p | yes e∉p with v∈e[p∷ps]
    ...   | here  v≈i∷p   = p , e⇿p , e∉p , v≈i∷p
    ...   | there v∈e[ps] = extendAll-∈ ps v∈e[ps]


{-
    extendAll-∉ : ∀ {i} {q : SimplePathⁿᵗ n} {i∉q ps} → All (q ≉_) ps → All (i ∷ q ∣ i∉q ≉_) (extendAll ps i)
    extendAll-∉ {_} [] = []
    extendAll-∉ {i} {ps = p ∷ ps} (q≉p ∷ q≉ps) with i ∉? p
    ... | no  i∈p = extendAll-∉ q≉ps
    ... | yes i∉p = (λ {(_ ∷ p≈q) → q≉p p≈q}) ∷ (extendAll-∉ q≉ps)

    extendAll! : ∀ {ps} → Uniqueₚ ps → ∀ i → Uniqueₚ (extendAll ps i)
    extendAll!       [] _ = []
    extendAll! {ps = p ∷ ps} (p∉ps ∷ ps!) i with i ∉? p
    ... | no  _ = extendAll! ps! i
    ... | yes _ = extendAll-∉ p∉ps ∷ extendAll! ps! i

    extendAll-length : ∀ {l ps} → All (λ p → length p ≡ l) ps → ∀ i → All (λ p → length p ≡ suc l) (extendAll ps i)
    extendAll-length [] _ = []
    extendAll-length {ps = p ∷ ps} (|p|≡l ∷ |ps|≡l) i with i ∉? p
    ... | no i∈p = extendAll-length |ps|≡l i
    ... | yes _  = cong suc |p|≡l ∷ extendAll-length |ps|≡l i

    #-extendAll : ∀ ps qs {i j} → i ≢ j → (extendAll ps i) #ₚ (extendAll qs j)
    #-extendAll ps qs i≢j (v∈extᵢps , v∈extⱼqs) with extendAll-∈ ps v∈extᵢps | extendAll-∈ qs v∈extⱼqs
    ... | _ , _ , v≈i∷p | _ , _ , v≈j∷q = p₀≢q₀⇨p≉q i≢j (≈-trans (≈-sym v≈i∷p) v≈j∷q)
    -}



  abstract
    
    allPathsOfLength : ℕ → List (SimplePathⁿᵗ n)
    allPathsOfLength 0       = [] ∷ []
    allPathsOfLength (suc l) = concat (map (extendAll (allPathsOfLength l)) (allFinPairs n))

    ∈-allPathsOfLength : ∀ p → p ∈ₚ (allPathsOfLength (length p))
    ∈-allPathsOfLength []                  = here ≈ₚ-refl
    ∈-allPathsOfLength ((i , j) ∷ p ∣ e⇿p ∣ e∉p) = 
      ∈-concat⁺′ Pₛ
        (∈-extendAll (∈-allPathsOfLength p))
        (∈-map⁺ F×Fₛ LPₛ
          (≈ₗₚ-reflexive ∘ cong (extendAll (allPathsOfLength (length p))))
          (∈-allFinPairs⁺ i j))
{-
    allPathsOfLength! : ∀ l → Uniqueₚ (allPathsOfLength l)
    allPathsOfLength! zero          = []
    allPathsOfLength! (suc zero)    = allPathsOfLength1! allSrcDst!
    allPathsOfLength! (suc (suc l)) = concat!⁺ Pₛ (All-map⁺₂ (extendAll! (allPathsOfLength! (suc l))) (allFin n)) (AllPairs-map⁺₂ (#-extendAll (allPathsOfLength (suc l)) (allPathsOfLength (suc l))) (allFin!⁺ n))

    allPathsOfLength-length : ∀ l → All (λ p → length p ≡ l) (allPathsOfLength l)
    allPathsOfLength-length zero          = []
    allPathsOfLength-length (suc zero)    = allPathsOfLength1-length1 allSrcDst
    allPathsOfLength-length (suc (suc l)) = concat⁺ (All-map⁺₂ (extendAll-length (allPathsOfLength-length (suc l))) (allFin n))

    l-resp-≈ : ∀ l → (λ p → length p ≡ l) Respects (_≈_ {n})
    l-resp-≈ _ x≈y |x|≡l  = ≡-trans (≡-sym (p≈q⇒|p|≡|q| x≈y)) |x|≡l

    #-≢-allPathsOfLength : ∀ {l k} → l ≢ k → (allPathsOfLength l) #ₚ (allPathsOfLength k)
    #-≢-allPathsOfLength {l} {k} l≢k (v∈pₗ , v∈pₖ) = l≢k (≡-trans (≡-sym (All-∈ Pₛ (l-resp-≈ l) (allPathsOfLength-length l) v∈pₗ)) (All-∈ Pₛ (l-resp-≈ k) (allPathsOfLength-length k) v∈pₖ))

    #-<-allPathsOfLength : ∀ {l k} → l < k → k < n → (allPathsOfLength l) #ₚ (allPathsOfLength k)
    #-<-allPathsOfLength l<k _ = #-≢-allPathsOfLength (<⇒≢ l<k)

    allPathsOfLength-sorted : ∀ l → AllPairs _≤ₗ_ (allPathsOfLength l)
    allPathsOfLength-sorted l = All⇒AllPairs (allPathsOfLength-length l) (λ |p|≡l |q|≡l → ≤-reflexive (≡-trans |p|≡l (≡-sym |q|≡l)))

    allPathsOfLength-inc : ∀ {l k} → l < k → k < n → All (λ p → All (p ≤ₗ_) (allPathsOfLength k)) (allPathsOfLength l)
    allPathsOfLength-inc {l} {k} l<k _ = mapₐ (λ {≡-refl → mapₐ (λ {≡-refl → <⇒≤ l<k}) (allPathsOfLength-length k)}) (allPathsOfLength-length l)
-}
    


    allPaths : List (SimplePathⁿᵗ n)
    allPaths = [] ∷ concat (applyUpTo allPathsOfLength n)
    
    ∈-allPaths : ∀ p → p ∈ₚ allPaths
    ∈-allPaths []                  = here ≈ₚ-refl
    ∈-allPaths (e ∷ p ∣ e⇿p ∣ e∉p) =
      there (∈-concat⁺′ Pₛ
        (∈-allPathsOfLength (e ∷ p ∣ e⇿p ∣ e∉p))
        (∈-applyUpTo⁺ LPₛ allPathsOfLength (|p|<n (nonEmpty e p e⇿p e∉p))))
{-
    allPaths! : Uniqueₚ allPaths
    allPaths! = concat!⁺ Pₛ
      (applyUpTo⁺₂ allPathsOfLength n allPathsOfLength!)
      (AllPairs-applyUpTo⁺₁ allPathsOfLength n #-<-allPathsOfLength)

    allPaths-sortedByLength : AllPairs _≤ₗ_ allPaths
    allPaths-sortedByLength = AllPairs-concat⁺
      (applyUpTo⁺₂ allPathsOfLength n allPathsOfLength-sorted)
      (AllPairs-applyUpTo⁺₁ allPathsOfLength n allPathsOfLength-inc )
    
  P : Uniset DPₛ
  P = allPaths , allPaths!

  enumeration : Enumeration DPₛ
  enumeration = record 
    { X             = P
    ; isEnumeration = ∈-allPaths
    }
-}
