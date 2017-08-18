open import Data.Fin using (Fin)
open import Data.Fin.Properties using () renaming (_≟_ to _≟F_)
open import Data.Nat using (ℕ; zero; suc; _<_)
open import Data.Nat.Properties using (<⇒≢)
open import Data.List using (List; []; _∷_; map; concat; allFin; applyUpTo)
open import Data.List.Any using (here; there)
open import Data.List.Any.Membership.Propositional using (_∈_)
open import Data.List.All using (All; []; _∷_) renaming (map to mapₐ)
open import Data.List.All.Properties using (applyUpTo⁺₂; concat⁺) 
open import Data.Product using (∃₂; _,_; _×_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary using (Setoid; DecSetoid; _Respects_)
open import Relation.Binary.List.Pointwise using () renaming (setoid to listSetoid)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; cong; cong₂) renaming (setoid to ≡-setoid; refl to ≡-refl; sym to ≡-sym; trans to ≡-trans)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Function using (_∘_)

open import RoutingLib.Data.List using (dfilter; combine)
open import RoutingLib.Data.List.All using ([]; _∷_)
open import RoutingLib.Data.List.All.Properties using (AllPairs-applyUpTo⁺₁; All-map⁺₂; AllPairs-map⁺₂; All-∈)
open import RoutingLib.Data.List.Uniqueness.Properties using (map!⁺; concat!⁺) -- combine!
open import RoutingLib.Data.List.Uniqueness.Propositional using (Unique; allFin!⁺; combine!⁺)
open import RoutingLib.Data.List.Any.Membership.Propositional using (∈-allFin⁺; ∈-combine⁺)
open import RoutingLib.Data.List.Any.Membership.Properties using (∈-map⁺; ∈-concat⁺; ∈-applyUpTo⁺)
open import RoutingLib.Data.List.Uniset using (Uniset; Enumeration; IsEnumeration)
open import RoutingLib.Data.Graph.SimplePath.NonEmpty
open import RoutingLib.Data.Graph.SimplePath.NonEmpty.Properties


module RoutingLib.Data.Graph.SimplePath.NonEmpty.Enumeration (n : ℕ) where

  -- Enumerating paths
  
  allSrcDst : List (Fin n × Fin n)
  allSrcDst = combine _,_ (allFin n) (allFin n)

  extendAll : List (SimplePathⁿᵗ n) → Fin n → List (SimplePathⁿᵗ n)
  extendAll []       _ = []
  extendAll (p ∷ ps) i with i ∉? p
  ... | no _    = extendAll ps i
  ... | yes i∉p = (i ∷ p ∣ i∉p) ∷ extendAll ps i

  allPathsOfLength1 : List (Fin n × Fin n) → List (SimplePathⁿᵗ n)
  allPathsOfLength1 [] = []
  allPathsOfLength1 ((i , j) ∷ xs) with i ≟F j
  ... | yes _   = allPathsOfLength1 xs
  ... | no  i≢j = (i ∺ j ∣ i≢j) ∷ allPathsOfLength1 xs

  allPathsOfLength : ℕ → List (SimplePathⁿᵗ n)
  allPathsOfLength zero          = []
  allPathsOfLength (suc zero)    = allPathsOfLength1 allSrcDst
  allPathsOfLength (suc (suc l)) = concat (map (extendAll (allPathsOfLength (suc l))) (allFin n))

  allPaths : List (SimplePathⁿᵗ n)
  allPaths = concat (applyUpTo allPathsOfLength n)


  private

    Fₛ : Setoid _ _
    Fₛ = ≡-setoid (Fin n)

    Pₛ : Setoid _ _
    Pₛ = ≈-setoid {n}

    DPₛ : DecSetoid _ _
    DPₛ = ≈-decSetoid {n}

    LPₛ : Setoid _ _
    LPₛ = listSetoid Pₛ

    open import Data.List.Any.Membership Pₛ using () renaming (_∈_ to _∈ₚ_; _∉_ to _∉ₚ_)
    open import RoutingLib.Data.List.Disjoint   Pₛ using () renaming (_#_ to _#ₚ_)
    open import RoutingLib.Data.List.Uniqueness Pₛ using () renaming (Unique to Uniqueₚ)
    open Setoid LPₛ using () renaming (reflexive to ≈ₗₚ-reflexive)



  abstract

    -- source and destination pairs

    revPairCong : {w x y z : Fin n} → w ≢ y ⊎ x ≢ z → (w , x) ≢ (y , z)
    revPairCong (inj₁ w≢w) ≡-refl = w≢w ≡-refl
    revPairCong (inj₂ x≢x) ≡-refl = x≢x ≡-refl

    ∈-allSrcDst : ∀ i j → (i , j) ∈ allSrcDst
    ∈-allSrcDst i j = ∈-combine⁺ _,_ (∈-allFin⁺ i) (∈-allFin⁺ j)

    allSrcDst! : Unique allSrcDst
    allSrcDst! = combine!⁺ _,_ revPairCong (allFin!⁺ n) (allFin!⁺ n)


    -- extensions

    ∈-extendAll : ∀ {i q i∉q ps} → q ∈ₚ ps → i ∷ q ∣ i∉q ∈ₚ extendAll ps i
    ∈-extendAll {i} {_} {i∉q} {p ∷ _} (here q≈p) with i ∉? p
    ... | no i∈p = contradiction (∉-resp-≈ q≈p i∉q) i∈p
    ... | yes _  = here (≡-refl ∷ q≈p)
    ∈-extendAll {i} {ps = p ∷ _} (there q∈ps) with i ∉? p
    ... | no  _ = ∈-extendAll q∈ps
    ... | yes _ = there (∈-extendAll q∈ps)

    extendAll-∈ : ∀ {i v} ps → v ∈ₚ extendAll ps i → ∃₂ λ q i∉q → v ≈ i ∷ q ∣ i∉q
    extendAll-∈ []  ()
    extendAll-∈ {i} (p ∷ ps) v∈e[p∷ps] with i ∉? p
    ... | no  _   = extendAll-∈ ps v∈e[p∷ps]
    ... | yes i∉p with v∈e[p∷ps]
    ...   | here  v≈i∷p = p , i∉p , v≈i∷p
    ...   | there v∈e[ps] = extendAll-∈ ps v∈e[ps]

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


    -- All paths of length 1

    ∈-allPathsOfLength1 : ∀ {i j} (i≢j : i ≢ j) {xs} → (i , j) ∈ xs → (i ∺ j ∣ i≢j) ∈ₚ allPathsOfLength1 xs
    ∈-allPathsOfLength1 {i} {j} i≢j (here ≡-refl) with i ≟F j
    ... | yes i≡j = contradiction i≡j i≢j
    ... | no  _   = here (≡-refl ∺ ≡-refl)
    ∈-allPathsOfLength1 i≢j {(k , l) ∷ _} (there ij∈xs) with k ≟F l
    ... | yes _ = ∈-allPathsOfLength1 i≢j ij∈xs
    ... | no  _ = there (∈-allPathsOfLength1 i≢j ij∈xs)

    allPathsOfLength1-≉ : ∀ {i j} (i≢j : i ≢ j) {xs} → All ((i , j) ≢_) xs → All (i ∺ j ∣ i≢j ≉_) (allPathsOfLength1 xs)
    allPathsOfLength1-≉ _   {[]}           _ = []
    allPathsOfLength1-≉ i≢j {(k , l) ∷ xs} (ij≢kl ∷ Pxs) with k ≟F l
    ... | yes _ = allPathsOfLength1-≉ i≢j Pxs
    ... | no  _ = (λ {(i≡k ∺ j≡l) → ij≢kl (cong₂ _,_ i≡k j≡l)}) ∷ allPathsOfLength1-≉ i≢j Pxs

    allPathsOfLength1! : ∀ {xs} → Unique xs → Uniqueₚ (allPathsOfLength1 xs)
    allPathsOfLength1! [] = []
    allPathsOfLength1! {(i , j) ∷ xs} (ij∉xs ∷ xs!) with i ≟F j
    ... | yes _   = allPathsOfLength1! xs!
    ... | no  i≢j = allPathsOfLength1-≉ i≢j ij∉xs ∷ allPathsOfLength1! xs!

    allPathsOfLength1-length1 : ∀ xs → All (λ p → length p ≡ 1) (allPathsOfLength1 xs)
    allPathsOfLength1-length1 []             = []
    allPathsOfLength1-length1 ((i , j) ∷ xs) with i ≟F j
    ... | yes _ = allPathsOfLength1-length1 xs
    ... | no  _ = ≡-refl ∷ allPathsOfLength1-length1 xs


    -- All paths of length l

    ∈-allPathsOfLength : ∀ p → p ∈ₚ (allPathsOfLength (length p))
    ∈-allPathsOfLength (i ∺ j ∣ _)           = ∈-allPathsOfLength1 _ (∈-allSrcDst i j)
    ∈-allPathsOfLength (i ∷ j ∺ k ∣ j≢k ∣ _) = ∈-concat⁺ Pₛ (∈-extendAll (∈-allPathsOfLength _)) (∈-map⁺ Fₛ LPₛ (≈ₗₚ-reflexive ∘ cong (extendAll (allPathsOfLength (length (j ∺ k ∣ j≢k))))) (∈-allFin⁺ i))
    ∈-allPathsOfLength (i ∷ j ∷ p ∣ j≢k ∣ _) = ∈-concat⁺ Pₛ (∈-extendAll (∈-allPathsOfLength _)) (∈-map⁺ Fₛ LPₛ (≈ₗₚ-reflexive ∘ cong (extendAll (allPathsOfLength (suc (length p))))) (∈-allFin⁺ i))

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


    -- All paths

    ∈-allPaths : ∀ p → p ∈ₚ allPaths
    ∈-allPaths p = ∈-concat⁺ Pₛ (∈-allPathsOfLength p) (∈-applyUpTo⁺ LPₛ allPathsOfLength (|p|<n p))

    allPaths! : Uniqueₚ allPaths
    allPaths! = concat!⁺ Pₛ (applyUpTo⁺₂ allPathsOfLength n allPathsOfLength!) (AllPairs-applyUpTo⁺₁ allPathsOfLength n #-<-allPathsOfLength)



  P : Uniset DPₛ
  P = allPaths , allPaths!

  enumeration : Enumeration DPₛ
  enumeration = record 
    { X             = P
    ; isEnumeration = ∈-allPaths
    }
